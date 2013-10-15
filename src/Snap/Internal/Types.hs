{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}

module Snap.Internal.Types where

------------------------------------------------------------------------------
import           Blaze.ByteString.Builder
import           Blaze.ByteString.Builder.Char.Utf8
import           Control.Applicative
import           Control.Exception hiding (bracket)
import           Control.Monad
import           Control.Monad.Base
import           Control.Monad.IO.Class
import           Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as S
import qualified Data.ByteString.Lazy.Char8 as L
import           Data.CaseInsensitive (CI)
import           Data.Int
import           Data.Maybe
import           Data.Time
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import           Data.Typeable
-- #if MIN_VERSION_base(4,6,0)
-- import           Prelude hiding (take)
-- #else
-- import           Prelude hiding (catch, take)
-- #endif
import           System.IO.Streams (InputStream, OutputStream)
import qualified System.IO.Streams as Streams
import           System.PosixCompat.Files hiding (setFileSize)
import           System.Posix.Types (FileOffset)
import           Unsafe.Coerce
------------------------------------------------------------------------------
import           Snap.Internal.Http.Types
import           Snap.Internal.Parsing (urlDecode)
import qualified Snap.Types.Headers as H
import qualified Data.Readable as R
------------------------------------------------------------------------------
import           Eff
import           OpenUnion1
import           ExtMTL


                             --------------------
                             -- The Snap Monad --
                             --------------------
{-|

'Snap' is the 'Monad' that user web handlers run in. 'Snap' gives you:

1. stateful access to fetch or modify an HTTP 'Request'

2. stateful access to fetch or modify an HTTP 'Response'

3. failure \/ 'Alternative' \/ 'MonadPlus' semantics: a 'Snap' handler can
   choose not to handle a given request, using 'empty' or its synonym 'pass',
   and you can try alternative handlers with the '<|>' operator:

   > a :: Snap String
   > a = pass
   >
   > b :: Snap String
   > b = return "foo"
   >
   > c :: Snap String
   > c = a <|> b             -- try running a, if it fails then try b

4. convenience functions ('writeBS', 'writeLBS', 'writeText', 'writeLazyText',
   'addToOutput') for queueing output to be written to the 'Response':

   > a :: (forall a . Enumerator a) -> Snap ()
   > a someEnumerator = do
   >     writeBS "I'm a strict bytestring"
   >     writeLBS "I'm a lazy bytestring"
   >     writeText "I'm strict text"
   >     addToOutput someEnumerator

5. early termination: if you call 'finishWith':

   > a :: Snap ()
   > a = do
   >   modifyResponse $ setResponseStatus 500 "Internal Server Error"
   >   writeBS "500 error"
   >   r <- getResponse
   >   finishWith r

   then any subsequent processing will be skipped and supplied 'Response'
   value will be returned from 'runSnap' as-is.

6. access to the 'IO' monad through a 'MonadIO' instance:

   > a :: Snap ()
   > a = liftIO fireTheMissiles

7. the ability to set or extend a timeout which will kill the handler thread
   after @N@ seconds of inactivity (the default is 20 seconds):

   > a :: Snap ()
   > a = setTimeout 30

8. throw and catch exceptions using a 'MonadBaseControl' instance:

   > import           Control.Exception.Lifted (SomeException, throwIO, catch)
   > foo :: Snap ()
   > foo = bar `catch` \(e::SomeException) -> baz
   >   where
   >     bar = throwIO FooException

9. log a message to the error log:

   > foo :: Snap ()
   > foo = logError "grumble."

You may notice that most of the type signatures in this module contain a
@(MonadSnap m) => ...@ typeclass constraint. 'MonadSnap' is a typeclass which,
in essence, says \"you can get back to the 'Snap' monad from here\". Using
'MonadSnap' you can extend the 'Snap' monad with additional functionality and
still have access to most of the 'Snap' functions without writing 'lift'
everywhere. Instances are already provided for most of the common monad
transformers ('ReaderT', 'WriterT', 'StateT', etc.).

-}

------------------------------------------------------------------------------
-- | 'MonadSnap' is a type class, analogous to 'MonadIO' for 'IO', that makes
-- it easy to wrap 'Snap' inside monad transformers.
-- class (Monad m, MonadIO m, MonadBaseControl IO m, MonadPlus m, Functor m,
--       Applicative m, Alternative m) => MonadSnap m where
--    liftSnap :: Snap a -> m a

-- Given ExtEff, this is just a constraint alias.
-- Note that we may need additional constraints for error handling and IO
-- in certain places, since the new Snap has less built in.

------------------------------------------------------------------------------
--data SnapResult a = SnapValue a
--                  | Zero Zero

------------------------------------------------------------------------------
type EscapeHttpHandler =  ((Int -> Int) -> IO ())    -- ^ timeout modifier
                       -> InputStream ByteString     -- ^ socket read end
                       -> OutputStream Builder       -- ^ socket write end
                       -> IO ()


------------------------------------------------------------------------------
data EscapeSnap = TerminateConnection SomeException
                | EscapeHttp EscapeHttpHandler
--                | PassOnProcessing
  deriving (Typeable)

data SnapControl = EscapeSnap EscapeSnap 
                 | EarlyTermination Response
                 | PassOnProcessing 
    deriving (Show, Typeable)

instance Exception EscapeSnap

instance Show EscapeSnap where
    show (TerminateConnection e) = "<terminated: " ++ show e ++ ">"
    show (EscapeHttp _)          = "<escape http>" 
--    show (PassOnProcessing)      = "Pass on processing"
------------------------------------------------------------------------------
--newtype EarlyTermination = EarlyTermination Response

-- newtype PassOnProcessing = Pass ()
------------------------------------------------------------------------------
data SnapS w = SnapS (SnapState -> SnapState) (SnapState -> w)
    --        | Zero PassOnProcessing
    deriving (Typeable)

runSnapS :: Eff (SnapS :> r) w -> SnapState -> Eff r (w, SnapState)
runSnapS m s = loop s (admin m)
  where
    loop s (Val x) = return (x,s)
    loop s (E u)   = handle_relay u (loop s) $ \(SnapS t k) ->
                        let s' = t s in s' `seq` loop s' (k s')

sput :: Member SnapS r => SnapState -> Eff r ()
sput s = send (\k -> inj (SnapS (const s) (\_ -> k ())))

-- | Local Snap version of 'get'.
sget :: Member SnapS r => Eff r SnapState
sget = send (\k -> inj (SnapS id k))

-- | Local Snap monad version of 'modify'.
smodify :: Member SnapS r => (SnapState -> SnapState) -> Eff r ()
smodify f = send (\k -> inj (SnapS f (\_ -> k ())))
------------------------------------------------------------------------------
data SnapState = SnapState
    { _snapRequest       :: Request
    , _snapResponse      :: Response
    , _snapLogError      :: ByteString -> IO ()
    , _snapModifyTimeout :: (Int -> Int) -> IO ()
    }


------------------------------------------------------------------------------
--instance MonadIO Snap where
--    liftIO m = Snap $! liftM SnapValue $! liftIO m


------------------------------------------------------------------------------
--instance (MonadBase IO) Snap where
--    liftBase = Snap . liftM SnapValue . liftBase


------------------------------------------------------------------------------
--instance (MonadBaseControl IO) Snap where
--    newtype StM Snap a = StSnap {
--           unStSnap :: StM (StateT SnapState IO) (SnapResult a)
--         }
-- 
--     liftBaseWith f = Snap $ liftM SnapValue $
--                      liftBaseWith $ \g' -> f $ \m ->
--                      liftM StSnap $ g' $ unSnap m
--     {-# INLINE liftBaseWith #-}
-- 
--     restoreM = Snap . restoreM . unStSnap
--     {-# INLINE restoreM #-}
-- 

------------------------------------------------------------------------------
instance (Snap r) => MonadPlus (Eff r) where
    mzero = throwError PassOnProcessing
    --send (\_ -> inj $! Zero $! PassOnProcessing)

    a `mplus` b = catchError a handle where
        handle PassOnProcessing = b
        handle e                = throwError e

------------------------------------------------------------------------------
instance Functor SnapS where
    fmap f (SnapS t k)   = SnapS t (f . k)
   -- fmap f (SnapZero z) = SnapZero z

------------------------------------------------------------------------------
instance (Snap r) => Alternative (Eff r) where
    empty = mzero
    (<|>) = mplus

instance (Snap r) => Applicative (Eff r) where
    pure = return
    (<*>) = ap
------------------------------------------------------------------------------
-- A ConstraintKinds type synonym, for simpler type signatures
-- Analogous to MonadSnap

type Snap r = ( Member SnapS r
              , Member (Exc SnapControl) r )

------------------------------------------------------------------------------
-- | The Typeable instance is here so Snap can be dynamically executed with
-- Hint.
--
-- Do we need a new version of this? or is the derived version sufficient?
-- snapTyCon :: TyCon
-- #if MIN_VERSION_base(4,4,0)
-- snapTyCon = mkTyCon3 "snap-core" "Snap.Core" "Snap"
-- #else
-- snapTyCon = mkTyCon "Snap.Core.Snap"
-- #endif
-- {-# NOINLINE snapTyCon #-}
-- 
-- instance Typeable1 Snap where
--     typeOf1 _ = mkTyConApp snapTyCon []
-- 

------------------------------------------------------------------------------
-- | Pass the request body stream to a consuming procedure, returning the
-- result.
--
-- If the iteratee you pass in here throws an exception, Snap will attempt to
-- clear the rest of the unread request body before rethrowing the exception.
-- If your iteratee used 'terminateConnection', however, Snap will give up and
-- immediately close the socket.
--
-- FIXME/TODO: reword above

runRequestBody :: (Snap r, MonadIO (Eff r)) =>
                  (InputStream ByteString -> IO a)
               -> Eff r a
runRequestBody proc = do
    bumpTimeout <- liftM ($ max 5) getTimeoutModifier
    req         <- getRequest
    body        <- liftIO $ Streams.throwIfTooSlow bumpTimeout 500 5 $
                            rqBody req
    run body

  where
    skip body = (Streams.skipToEof body) `catch` tooSlow

    tooSlow (e :: Streams.RateTooSlowException) =
        throw . TerminateConnection . SomeException $ e

    run body = liftIO $ (do
        x <- proc body
        Streams.skipToEof body
        return x) `catches` handlers
      where
        handlers = [ Handler tooSlow, Handler other ]
        other (e :: SomeException) = skip body >> throwIO e


------------------------------------------------------------------------------
-- | Returns the request body as a lazy bytestring. /New in 0.6./
readRequestBody :: (Snap r, MonadIO (Eff r)) =>
                   Int64  -- ^ size of the largest request body we're willing
                          -- to accept. If a request body longer than this is
                          -- received, a 'TooManyBytesReadException' is
                          -- thrown. See 'takeNoMoreThan'.
                -> Eff r L.ByteString
readRequestBody sz = liftM L.fromChunks $ runRequestBody f
  where
    f str = Streams.throwIfProducesMoreThan sz str >>= Streams.toList


------------------------------------------------------------------------------
-- | Normally Snap is careful to ensure that the request body is fully
-- consumed after your web handler runs, but before the 'Response' body
-- is streamed out the socket. If you want to transform the request body into
-- some output in O(1) space, you should use this function.
--
-- Take care: in order for this to work, the HTTP client must be written with
-- input-to-output streaming in mind.
--
-- Note that upon calling this function, response processing finishes early as
-- if you called 'finishWith'. Make sure you set any content types, headers,
-- cookies, etc. before you call this function.
--
transformRequestBody :: (Snap r, MonadIO (Eff r)) => 
                        (InputStream ByteString -> IO (InputStream ByteString))
                         -- ^ the 'InputStream' from the 'Request' is passed to
                         -- this function, and then the resulting 'InputStream'
                         -- is fed to the output.
                     -> Eff r ()
transformRequestBody trans = do
    req     <- getRequest
    is      <- liftIO ((trans $ rqBody req) >>=
                         Streams.mapM (return . fromByteString))
    origRsp <- getResponse
    let rsp = setResponseBody (\out -> Streams.connect is out >> return out) $
              origRsp { rspTransformingRqBody = True }
    finishWith rsp


------------------------------------------------------------------------------
-- | Short-circuits a 'Snap' monad action early, storing the given
-- 'Response' value in its state.
finishWith :: Snap r => Response -> Eff r a
finishWith resp = throwError $ EarlyTermination resp
{-# INLINE finishWith #-}


------------------------------------------------------------------------------
-- | Capture the flow of control in case a handler calls 'finishWith'.
--
-- /WARNING/: in the event of a call to 'transformRequestBody' it is possible
-- to violate HTTP protocol safety when using this function. If you call
-- 'catchFinishWith' it is suggested that you do not modify the body of the
-- 'Response' which was passed to the 'finishWith' call.
catchFinishWith :: Snap r => Eff r a -> Eff r (Either Response a)
catchFinishWith = flip catchError finish . fmap Right
  where
    finish (EarlyTermination resp) = return $ Left resp
{-# INLINE catchFinishWith #-}


------------------------------------------------------------------------------
-- | Fails out of a 'Snap' monad action.  This is used to indicate
-- that you choose not to handle the given request within the given
-- handler.
pass :: Snap r => Eff r a
pass = empty


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only if the request's HTTP method matches
-- the given method.
method :: Snap r => Method -> Eff r a -> Eff r a
method m action = do
    req <- getRequest
    unless (rqMethod req == m) pass
    action
{-# INLINE method #-}


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only if the request's HTTP method matches
-- one of the given methods.
methods :: Snap r => [Method] -> Eff r a -> Eff r a
methods ms action = do
    req <- getRequest
    unless (rqMethod req `elem` ms) pass
    action
{-# INLINE methods #-}


------------------------------------------------------------------------------
-- Appends n bytes of the path info to the context path with a
-- trailing slash.
updateContextPath :: Int -> Request -> Request
updateContextPath n req | n > 0     = req { rqContextPath = ctx
                                          , rqPathInfo    = pinfo }
                        | otherwise = req
  where
    ctx'  = S.take n (rqPathInfo req)
    ctx   = S.concat [rqContextPath req, ctx', "/"]
    pinfo = S.drop (n+1) (rqPathInfo req)


------------------------------------------------------------------------------
-- Runs a 'Snap' monad action only if the 'rqPathInfo' matches the given
-- predicate.
pathWith :: Snap r
         => (ByteString -> ByteString -> Bool)
         -> ByteString
         -> Eff r a
         -> Eff r a
pathWith c p action = do
    req <- getRequest
    unless (c p (rqPathInfo req)) pass
    localRequest (updateContextPath $ S.length p) action


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only when the 'rqPathInfo' of the request
-- starts with the given path. For example,
--
-- > dir "foo" handler
--
-- Will fail if 'rqPathInfo' is not \"@\/foo@\" or \"@\/foo\/...@\", and will
-- add @\"foo\/\"@ to the handler's local 'rqContextPath'.
dir :: Snap r
    => ByteString  -- ^ path component to match
    -> Eff r a         -- ^ handler to run
    -> Eff r a
dir = pathWith f
  where
    f dr pinfo = dr == x
      where
        (x,_) = S.break (=='/') pinfo
{-# INLINE dir #-}


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only for requests where 'rqPathInfo' is
-- exactly equal to the given string. If the path matches, locally sets
-- 'rqContextPath' to the old value of 'rqPathInfo', sets 'rqPathInfo'=\"\",
-- and runs the given handler.
path :: Snap r
     => ByteString  -- ^ path to match against
     -> Eff r a         -- ^ handler to run
     -> Eff r a
path = pathWith (==)
{-# INLINE path #-}


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only when the first path component is
-- successfully parsed as the argument to the supplied handler function.
--
-- Note that the path segment is url-decoded prior to being passed to 'fromBS';
-- this is new as of snap-core 0.10.
pathArg :: (R.Readable a, Snap r)
        => (a -> Eff r b)
        -> Eff r b
pathArg f = do
    req <- getRequest
    let (p,_) = S.break (=='/') (rqPathInfo req)
    p' <- maybe mzero return $ urlDecode p
    a <- R.fromBS p'
    localRequest (updateContextPath $ S.length p) (f a)


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only when 'rqPathInfo' is empty.
ifTop :: Snap r => Eff r a -> Eff r a
ifTop = path ""
{-# INLINE ifTop #-}

------------------------------------------------------------------------------
-- | Grabs the 'Request' object out of the 'Snap' monad.
getRequest :: Snap r => Eff r Request
getRequest = liftM _snapRequest sget
{-# INLINE getRequest #-}


------------------------------------------------------------------------------
-- | Grabs something out of the 'Request' object, using the given projection
-- function. See 'gets'.
getsRequest :: Snap r => (Request -> a) -> Eff r a
getsRequest f = liftM (f . _snapRequest) sget
{-# INLINE getsRequest #-}


------------------------------------------------------------------------------
-- | Grabs the 'Response' object out of the 'Snap' monad.
getResponse :: Snap r => Eff r Response
getResponse = liftM _snapResponse sget
{-# INLINE getResponse #-}


------------------------------------------------------------------------------
-- | Grabs something out of the 'Response' object, using the given projection
-- function. See 'gets'.
getsResponse :: Snap r => (Response -> a) -> Eff r a
getsResponse f = liftM (f . _snapResponse) sget
{-# INLINE getsResponse #-}


------------------------------------------------------------------------------
-- | Puts a new 'Response' object into the 'Snap' monad.
putResponse :: Snap r => Response -> Eff r ()
putResponse r = smodify $ \ss -> ss { _snapResponse = r }
{-# INLINE putResponse #-}


------------------------------------------------------------------------------
-- | Puts a new 'Request' object into the 'Snap' monad.
putRequest :: Snap r => Request -> Eff r ()
putRequest r = smodify $ \ss -> ss { _snapRequest = r }
{-# INLINE putRequest #-}


------------------------------------------------------------------------------
-- | Modifies the 'Request' object stored in a 'Snap' monad.
modifyRequest :: Snap r => (Request -> Request) -> Eff r ()
modifyRequest f = smodify $ \ss -> ss { _snapRequest = f $ _snapRequest ss }
{-# INLINE modifyRequest #-}


------------------------------------------------------------------------------
-- | Modifes the 'Response' object stored in a 'Snap' monad.
modifyResponse :: Snap r => (Response -> Response) -> Eff r ()
modifyResponse f = 
     smodify $ \ss -> ss { _snapResponse = f $ _snapResponse ss }
{-# INLINE modifyResponse #-}


------------------------------------------------------------------------------
-- | Performs a redirect by setting the @Location@ header to the given target
-- URL/path and the status code to 302 in the 'Response' object stored in a
-- 'Snap' monad. Note that the target URL is not validated in any way.
-- Consider using 'redirect\'' instead, which allows you to choose the correct
-- status code.
redirect :: Snap r => ByteString -> Eff r a
redirect target = redirect' target 302
{-# INLINE redirect #-}


------------------------------------------------------------------------------
-- | Performs a redirect by setting the @Location@ header to the given target
-- URL/path and the status code (should be one of 301, 302, 303 or 307) in the
-- 'Response' object stored in a 'Snap' monad. Note that the target URL is not
-- validated in any way.
redirect' :: Snap r => ByteString -> Int -> Eff r a
redirect' target status = do
    r <- getResponse

    finishWith
        $ setResponseCode status
        $ setContentLength 0
        $ modifyResponseBody (const $ return . id)
        $ setHeader "Location" target r

{-# INLINE redirect' #-}


------------------------------------------------------------------------------
-- | Log an error message in the 'Snap' monad
logError :: (Snap r, MonadIO (Eff r)) => ByteString -> Eff r ()
logError s = liftM _snapLogError sget >>= (\l -> liftIO $ l s)
{-# INLINE logError #-}


------------------------------------------------------------------------------
-- | Adds the output from the given enumerator to the 'Response'
-- stored in the 'Snap' monad state.
addToOutput :: Snap r
            => (OutputStream Builder -> IO (OutputStream Builder))
                    -- ^ output to add
            -> Eff r ()
addToOutput enum = modifyResponse $ modifyResponseBody (c enum)
  where
    c a b = \out -> b out >>= a

------------------------------------------------------------------------------
-- | Adds the given 'Builder' to the body of the 'Response' stored in the
-- | 'Snap' monad state.
writeBuilder :: Snap r => Builder -> Eff r ()
writeBuilder b = addToOutput f
  where
    f str = Streams.write (Just b) str >> return str
{-# INLINE writeBuilder #-}


------------------------------------------------------------------------------
-- | Adds the given strict 'ByteString' to the body of the 'Response' stored
-- in the 'Snap' monad state.
--
-- Warning: This function is intentionally non-strict. If any pure
-- exceptions are raised by the expression creating the 'ByteString',
-- the exception won't actually be raised within the Snap handler.
writeBS :: Snap r => ByteString -> Eff r ()
writeBS s = writeBuilder $ fromByteString s


------------------------------------------------------------------------------
-- | Adds the given lazy 'L.ByteString' to the body of the 'Response' stored
-- in the 'Snap' monad state.
--
-- Warning: This function is intentionally non-strict. If any pure
-- exceptions are raised by the expression creating the 'ByteString',
-- the exception won't actually be raised within the Snap handler.
writeLBS :: Snap r => L.ByteString -> Eff r ()
writeLBS s = writeBuilder $ fromLazyByteString s


------------------------------------------------------------------------------
-- | Adds the given strict 'T.Text' to the body of the 'Response' stored in
-- the 'Snap' monad state.
--
-- Warning: This function is intentionally non-strict. If any pure
-- exceptions are raised by the expression creating the 'ByteString',
-- the exception won't actually be raised within the Snap handler.
writeText :: Snap r => T.Text -> Eff r ()
writeText s = writeBuilder $ fromText s


------------------------------------------------------------------------------
-- | Adds the given lazy 'LT.Text' to the body of the 'Response' stored in the
-- 'Snap' monad state.
--
-- Warning: This function is intentionally non-strict. If any pure
-- exceptions are raised by the expression creating the 'ByteString',
-- the exception won't actually be raised within the Snap handler.
writeLazyText :: Snap r => LT.Text -> Eff r ()
writeLazyText s = writeBuilder $ fromLazyText s


------------------------------------------------------------------------------
-- | Sets the output to be the contents of the specified file.
--
-- Calling 'sendFile' will overwrite any output queued to be sent in the
-- 'Response'. If the response body is not modified after the call to
-- 'sendFile', Snap will use the efficient @sendfile()@ system call on
-- platforms that support it.
--
-- If the response body is modified (using 'modifyResponseBody'), the file
-- will be read using @mmap()@.
sendFile :: Snap r => FilePath -> Eff r ()
sendFile f = modifyResponse $ \r -> r { rspBody = SendFile f Nothing }


------------------------------------------------------------------------------
-- | Sets the output to be the contents of the specified file, within the
-- given (start,end) range.
--
-- Calling 'sendFilePartial' will overwrite any output queued to be sent in
-- the 'Response'. If the response body is not modified after the call to
-- 'sendFilePartial', Snap will use the efficient @sendfile()@ system call on
-- platforms that support it.
--
-- If the response body is modified (using 'modifyResponseBody'), the file
-- will be read using @mmap()@.
sendFilePartial :: Snap r  => FilePath -> (Int64,Int64) -> Eff r ()
sendFilePartial f rng = modifyResponse $ \r ->
                        r { rspBody = SendFile f (Just rng) }


------------------------------------------------------------------------------
-- | Runs a 'Snap' action with a locally-modified 'Request' state
-- object. The 'Request' object in the Snap monad state after the call
-- to localRequest will be unchanged.
localRequest :: Snap r => (Request -> Request) -> Eff r a -> Eff r a
localRequest f m = do
    req <- getRequest

    runAct req <|> (putRequest req >> pass)

  where
    runAct req = do
        modifyRequest f
        result <- m
        putRequest req
        return result
{-# INLINE localRequest #-}


------------------------------------------------------------------------------
-- | Fetches the 'Request' from state and hands it to the given action.
withRequest :: Snap r => (Request -> Eff r a) -> Eff r a
withRequest = (getRequest >>=)
{-# INLINE withRequest #-}


------------------------------------------------------------------------------
-- | Fetches the 'Response' from state and hands it to the given action.
withResponse :: Snap r => (Response -> Eff r a) -> Eff r a
withResponse = (getResponse >>=)
{-# INLINE withResponse #-}


------------------------------------------------------------------------------
-- | Modifies the 'Request' in the state to set the 'rqRemoteAddr'
-- field to the value in the X-Forwarded-For header. If the header is
-- not present, this action has no effect.
--
-- This action should be used only when working behind a reverse http
-- proxy that sets the X-Forwarded-For header. This is the only way to
-- ensure the value in the X-Forwarded-For header can be trusted.
--
-- This is provided as a filter so actions that require the remote
-- address can get it in a uniform manner. It has specifically limited
-- functionality to ensure that its transformation can be trusted,
-- when used correctly.
ipHeaderFilter :: Snap r => Eff r ()
ipHeaderFilter = ipHeaderFilter' "x-forwarded-for"


------------------------------------------------------------------------------
-- | Modifies the 'Request' in the state to set the 'rqRemoteAddr'
-- field to the value from the header specified.  If the header
-- specified is not present, this action has no effect.
--
-- This action should be used only when working behind a reverse http
-- proxy that sets the header being looked at. This is the only way to
-- ensure the value in the header can be trusted.
--
-- This is provided as a filter so actions that require the remote
-- address can get it in a uniform manner. It has specifically limited
-- functionality to ensure that its transformation can be trusted,
-- when used correctly.
ipHeaderFilter' :: Snap r => CI ByteString -> Eff r ()
ipHeaderFilter' header = do
    headerContents <- getHeader header <$> getRequest

    let whitespace = " \t\r\n"
        ipChrs = ".0123456789"
        trim f s = f (`elem` s)

        clean = trim S.takeWhile ipChrs . trim S.dropWhile whitespace
        setIP ip = modifyRequest $ \rq -> rq { rqClientAddr = clean ip }
    maybe (return $! ()) setIP headerContents


------------------------------------------------------------------------------
-- | This function brackets a Snap action in resource acquisition and
-- release. This is provided because MonadCatchIO's 'bracket' function
-- doesn't work properly in the case of a short-circuit return from
-- the action being bracketed.
--
-- In order to prevent confusion regarding the effects of the
-- aquisition and release actions on the Snap state, this function
-- doesn't accept Snap actions for the acquire or release actions.
--
-- This function will run the release action in all cases where the
-- acquire action succeeded.  This includes the following behaviors
-- from the bracketed Snap action.
--
-- 1. Normal completion
--
-- 2. Short-circuit completion, either from calling 'fail' or 'finishWith'
--
-- 3. An exception being thrown.
-- bracketSnapOld :: IO a -> (a -> IO b) -> (a -> Snap c) -> Snap c
-- bracketSnapOld before after thing = mask $ \restore -> Snap $ do
--     a <- liftIO before
--     let after' = liftIO $ after a
--     r <- unSnap (restore $ thing a) `onException` after'
--     _ <- after'
--     return r

-- Not yet asynchronous-excetion-safe
bracketSnap :: ( Snap r
               , MemberU2 Lift (Lift IO) r
               , Member Bracket r ) => 
               IO a -> (a -> IO b) -> (a -> Eff r c) -> Eff r c
bracketSnap before after thing = bracket before after thing

------------------------------------------------------------------------------
-- | This exception is thrown if the handler you supply to 'runSnap' fails.
data NoHandlerException = NoHandlerException String
   deriving (Eq, Typeable)


------------------------------------------------------------------------------
instance Show NoHandlerException where
    show (NoHandlerException e) = "No handler for request: failure was " ++ e


------------------------------------------------------------------------------
instance Exception NoHandlerException


------------------------------------------------------------------------------
-- | Terminate the HTTP session with the given exception.
terminateConnection :: (Exception e, Snap r) => e -> Eff r a
terminateConnection =
    throwError . EscapeSnap . TerminateConnection . SomeException


------------------------------------------------------------------------------
-- | Terminate the HTTP session and hand control to some external handler,
-- escaping all further HTTP traffic.
--
-- The external handler takes two arguments: a function to modify the thread's
-- timeout, and a write end to the socket.
escapeHttp :: Snap r =>
              EscapeHttpHandler
           -> Eff r ()
escapeHttp = throwError . EscapeSnap . EscapeHttp

-- BD: Start here

------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action.
runSnap :: Eff (Exc SnapControl :> SnapS :> Bracket :> Lift IO :> Void) a
        -> (ByteString -> IO ())
        -> ((Int -> Int) -> IO ())
        -> Request
        -> IO (Request, Response)
runSnap m logerr timeoutAction req = runLift
                                   . finalize
                                   . runBracket
                                   . flip runSnapS ss
                                   $ (runError m >>= handleSC)
  where
    handleSC (Right _ )                  = return ()
    handleSC (Left PassOnProcessing)     = putResponse' fourohfour
    handleSC (Left (EarlyTermination r)) = putResponse' r
    handleSC (Left (EscapeSnap e))       = throw e


    finalize :: Eff (Lift IO :> Void) (a, SnapState)
             -> Eff (Lift IO :> Void) (Request, Response)
    finalize m = do
        (_, ss') <- m
        let req  = _snapRequest ss'
            resp = _snapResponse ss'
        resp' <- liftIO $ fixupResponse req resp
        return (req, resp')

    -- We need a more general version here, because we've already
    -- removed the SnapControl layer.
    putResponse' r = smodify $ \s -> s { _snapResponse = r }

    --------------------------------------------------------------------------
    fourohfour = do
        clearContentLength                  $
          setResponseStatus 404 "Not Found" $
          setResponseBody enum404           $
          emptyResponse

    --------------------------------------------------------------------------
    enum404 out = do
        is <- Streams.fromList html
        Streams.connect is out
        return out

    --------------------------------------------------------------------------
    html = map fromByteString [ "<!DOCTYPE html>\n"
                              , "<html>\n"
                              , "<head>\n"
                              , "<title>Not found</title>\n"
                              , "</head>\n"
                              , "<body>\n"
                              , "<code>No handler accepted \""
                              , rqURI req
                              , "\"</code>\n</body></html>"
                              ]

    --------------------------------------------------------------------------
    dresp = emptyResponse { rspHttpVersion = rqVersion req }

    --------------------------------------------------------------------------
    ss = SnapState req dresp logerr timeoutAction
{-# INLINE runSnap #-}



--------------------------------------------------------------------------
-- | Post-process a finalized HTTP response:
--
-- * fixup content-length header
-- * properly handle 204/304 responses
-- * if request was HEAD, remove response body
--
-- Note that we do NOT deal with transfer-encoding: chunked or "connection:
-- close" here.
fixupResponse :: Request -> Response -> IO Response
fixupResponse req rsp = {-# SCC "fixupResponse" #-} do
    let code = rspStatus rsp
    let rsp' = if code == 204 || code == 304
                 then handle304 rsp
                 else rsp

    rsp'' <- do
        z <- case rspBody rsp' of
               (Stream _)                -> return rsp'
               (SendFile f Nothing)      -> setFileSize f rsp'
               (SendFile _ (Just (s,e))) -> return $!
                                            setContentLength (e-s) rsp'

        return $!
          case rspContentLength z of
            Nothing   -> deleteHeader "Content-Length" z
            (Just sz) -> setHeader "Content-Length"
                                   (toByteString $ fromShow sz)
                                   z

    -- HEAD requests cannot have bodies per RFC 2616 sec. 9.4
    if rqMethod req == HEAD
      then return $! deleteHeader "Transfer-Encoding" $
           rsp'' { rspBody = Stream $ return . id }
      else return $! rsp''

  where
    --------------------------------------------------------------------------
    setFileSize :: FilePath -> Response -> IO Response
    setFileSize fp r = {-# SCC "setFileSize" #-} do
        fs <- liftM fromIntegral $ getFileSize fp
        return $! r { rspContentLength = Just fs }

    ------------------------------------------------------------------------------
    getFileSize :: FilePath -> IO FileOffset
    getFileSize fp = liftM fileSize $ getFileStatus fp

    --------------------------------------------------------------------------
    handle304 :: Response -> Response
    handle304 r = setResponseBody (return . id) $
                  updateHeaders (H.delete "Transfer-Encoding") $
                  clearContentLength r
{-# INLINE fixupResponse #-}


------------------------------------------------------------------------------
evalSnap :: Eff (Exc SnapControl :> SnapS :> Bracket :> Lift IO :> Void) a
         -> (ByteString -> IO ())
         -> ((Int -> Int) -> IO ())
         -> Request
         -> IO a
evalSnap m logerr timeoutAction req = fmap fst . runLift . runBracket
                                    . flip runSnapS ss
                                    $ (runError m >>= handleSC)

  where
    handleSC (Right v )                  = return v
    handleSC (Left PassOnProcessing)     = throw $ NoHandlerException "pass"
    handleSC (Left (EscapeSnap e))       = throw e
    handleSC (Left (EarlyTermination r)) = throw $ ErrorCall "no value"

    dresp = emptyResponse { rspHttpVersion = rqVersion req }
    ss = SnapState req dresp logerr timeoutAction
{-# INLINE evalSnap #-}


------------------------------------------------------------------------------
getParamFrom :: Snap r =>
                (ByteString -> Request -> Maybe [ByteString])
             -> ByteString
             -> Eff r (Maybe ByteString)
getParamFrom f k = do
    rq <- getRequest
    return $! liftM (S.intercalate " ") $ f k rq
{-# INLINE getParamFrom #-}


------------------------------------------------------------------------------
-- | See 'rqParam'. Looks up a value for the given named parameter in the
-- 'Request'. If more than one value was entered for the given parameter name,
-- 'getParam' gloms the values together with:
--
-- @    'S.intercalate' \" \"@
--
getParam :: Snap r
         => ByteString          -- ^ parameter name to look up
         -> Eff r (Maybe ByteString)
getParam = getParamFrom rqParam
{-# INLINE getParam #-}


------------------------------------------------------------------------------
-- | See 'rqPostParam'. Looks up a value for the given named parameter in the
-- POST form parameters mapping in 'Request'. If more than one value was
-- entered for the given parameter name, 'getPostParam' gloms the values
-- together with:
--
-- @    'S.intercalate' \" \"@
--
getPostParam :: Snap r
             => ByteString          -- ^ parameter name to look up
             -> Eff r (Maybe ByteString)
getPostParam = getParamFrom rqPostParam
{-# INLINE getPostParam #-}


------------------------------------------------------------------------------
-- | See 'rqQueryParam'. Looks up a value for the given named parameter in the
-- query string parameters mapping in 'Request'. If more than one value was
-- entered for the given parameter name, 'getQueryParam' gloms the values
-- together with:
--
-- @    'S.intercalate' \" \"@
--
getQueryParam :: Snap r
              => ByteString          -- ^ parameter name to look up
              -> Eff r (Maybe ByteString)
getQueryParam = getParamFrom rqQueryParam
{-# INLINE getQueryParam #-}


------------------------------------------------------------------------------
-- | See 'rqParams'. Convenience function to return 'Params' from the
-- 'Request' inside of a 'MonadSnap' instance.
getParams :: Snap r => Eff r Params
getParams = getRequest >>= return . rqParams


------------------------------------------------------------------------------
-- | See 'rqParams'. Convenience function to return 'Params' from the
-- 'Request' inside of a 'MonadSnap' instance.
getPostParams :: Snap r => Eff r Params
getPostParams = getRequest >>= return . rqPostParams


------------------------------------------------------------------------------
-- | See 'rqParams'. Convenience function to return 'Params' from the
-- 'Request' inside of a 'MonadSnap' instance.
getQueryParams :: Snap r => Eff r Params
getQueryParams = getRequest >>= return . rqQueryParams


------------------------------------------------------------------------------
-- | Gets the HTTP 'Cookie' with the specified name.
getCookie :: Snap r
          => ByteString
          -> Eff r (Maybe Cookie)
getCookie name = withRequest $
    return . listToMaybe . filter (\c -> cookieName c == name) . rqCookies


------------------------------------------------------------------------------
-- | Gets the HTTP 'Cookie' with the specified name and decodes it.  If the
-- decoding fails, the handler calls pass.
readCookie :: (Snap r, R.Readable a)
           => ByteString
           -> Eff r a
readCookie name = maybe pass (R.fromBS . cookieValue) =<< getCookie name


------------------------------------------------------------------------------
-- | Expire the given 'Cookie' in client's browser.
expireCookie :: (Snap r)
             => ByteString
             -- ^ Cookie name
             -> Maybe ByteString
             -- ^ Cookie domain
             -> Eff r ()
expireCookie nm dm = do
  let old = UTCTime (ModifiedJulianDay 0) 0
  modifyResponse $ addResponseCookie
                 $ Cookie nm "" (Just old) Nothing dm False False


------------------------------------------------------------------------------
-- | Causes the handler thread to be killed @n@ seconds from now.
setTimeout :: (Snap r, MonadIO (Eff r)) => Int -> Eff r ()
setTimeout = modifyTimeout . const


------------------------------------------------------------------------------
-- | Causes the handler thread to be killed at least @n@ seconds from now.
extendTimeout :: (Snap r, MonadIO (Eff r)) => Int -> Eff r ()
extendTimeout = modifyTimeout . max


------------------------------------------------------------------------------
-- | Modifies the amount of time remaining before the request times out.
modifyTimeout :: (Snap r, MonadIO (Eff r)) => (Int -> Int) -> Eff r ()
modifyTimeout f = do
    m <- getTimeoutModifier
    liftIO $ m f


------------------------------------------------------------------------------
-- | Returns an 'IO' action which you can use to modify the timeout value.
getTimeoutModifier :: Snap r => Eff r ((Int -> Int) -> IO ())
getTimeoutModifier = liftM _snapModifyTimeout sget
