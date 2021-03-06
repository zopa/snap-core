{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE StandaloneDeriving         #-}
#endif
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Snap.Internal.Types
  ( MonadSnap(..)
  , SnapResult(..)
  , EscapeHttpHandler
  , EscapeSnap(..)
  , Zero(..)
  , Snap(..)
  , SnapState(..)
  , runRequestBody
  , readRequestBody
  , transformRequestBody
  , finishWith
  , catchFinishWith
  , pass
  , method
  , methods
  , updateContextPath
  , pathWith
  , dir
  , path
  , pathArg
  , ifTop
  , sget
  , smodify
  , getRequest
  , getResponse
  , getsRequest
  , getsResponse
  , putRequest
  , putResponse
  , modifyRequest
  , modifyResponse
  , redirect
  , redirect'
  , logError
  , addToOutput
  , writeBuilder
  , writeBS
  , writeLBS
  , writeText
  , writeLazyText
  , sendFile
  , sendFilePartial
  , localRequest
  , withRequest
  , withResponse
  , ipHeaderFilter
  , ipHeaderFilter'
  , bracketSnap
  , NoHandlerException(..)
  , terminateConnection
  , escapeHttp
  , runSnap
  , fixupResponse
  , evalSnap
  , getParamFrom
  , getParam
  , getPostParam
  , getQueryParam
  , getParams
  , getPostParams
  , getQueryParams
  , getCookie
  , readCookie
  , expireCookie
  , setTimeout
  , extendTimeout
  , modifyTimeout
  , getTimeoutModifier
  , module Snap.Internal.Http.Types
  ) where

------------------------------------------------------------------------------
import           Blaze.ByteString.Builder           (Builder, fromByteString, fromLazyByteString)
import           Blaze.ByteString.Builder.Char.Utf8 (fromLazyText, fromText)
import           Control.Applicative                (Alternative ((<|>), empty), Applicative ((<*>), pure), (<$>))
import           Control.Exception.Lifted           (ErrorCall (..), Exception, Handler (..), SomeException (..), catch, catches, mask, onException, throwIO)
import           Control.Monad                      (Functor (..), Monad (..), MonadPlus (..), ap, liftM, unless, (=<<))
import           Control.Monad.Base                 (MonadBase (..))
import           Control.Monad.IO.Class             (MonadIO (..))
import           Control.Monad.Trans.Control        (MonadBaseControl (..))
import           Control.Monad.Trans.State          (StateT (..))
import           Data.ByteString.Char8              (ByteString)
import qualified Data.ByteString.Char8              as S (break, concat, drop, dropWhile, intercalate, length, take, takeWhile)
import qualified Data.ByteString.Internal           as S (create, inlinePerformIO)
import qualified Data.ByteString.Lazy.Char8         as L (ByteString, fromChunks)
import           Data.CaseInsensitive               (CI)
import           Data.Maybe                         (Maybe (..), listToMaybe, maybe)
import qualified Data.Text                          as T (Text)
import qualified Data.Text.Lazy                     as LT (Text)
import           Data.Time                          (Day (ModifiedJulianDay), UTCTime (UTCTime))
import           Data.Typeable                      (TyCon, Typeable, Typeable1 (..), mkTyCon3, mkTyConApp)
import           Data.Word                          (Word64, Word8)
import           Foreign.Ptr                        (Ptr, plusPtr)
import           Foreign.Storable                   (poke)
import           Prelude                            (Bool (..), Either (..), Eq (..), FilePath, IO, Int, Num (..), Ord (..), Show (..), String, const, divMod, elem, filter, fromIntegral, id, map, max, otherwise, quot, ($), ($!), (++), (.), (||))
import           System.IO.Streams                  (InputStream, OutputStream)
import qualified System.IO.Streams                  as Streams
import           System.Posix.Types                 (FileOffset)
import           System.PosixCompat.Files           (fileSize, getFileStatus)
------------------------------------------------------------------------------
import qualified Data.Readable                      as R
import           Snap.Internal.Http.Types           (Cookie (..), HasHeaders (..), HttpVersion, Method (..), Params, Request (..), Response (..), ResponseBody (..), StreamProc, addHeader, addResponseCookie, c_format_http_time, c_format_log_time, c_parse_http_time, clearContentLength, deleteHeader, deleteResponseCookie, emptyResponse, formatHttpTime, formatLogTime, getHeader, getResponseCookie, getResponseCookies, listHeaders, modifyResponseBody, modifyResponseCookie, normalizeMethod, parseHttpTime, rqModifyParams, rqParam, rqPostParam, rqQueryParam, rqSetParam, rspBodyMap, rspBodyToEnum, setContentLength, setContentType, setHeader, setResponseBody, setResponseCode, setResponseStatus, set_c_locale, statusReasonMap, toStr)
import           Snap.Internal.Parsing              (urlDecode)
import qualified Snap.Types.Headers                 as H
------------------------------------------------------------------------------


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
class (Monad m, MonadIO m, MonadBaseControl IO m, MonadPlus m, Functor m,
       Applicative m, Alternative m) => MonadSnap m where
    liftSnap :: Snap a -> m a


------------------------------------------------------------------------------
data SnapResult a = SnapValue a
                  | Zero Zero


------------------------------------------------------------------------------
type EscapeHttpHandler =  ((Int -> Int) -> IO ())    -- ^ timeout modifier
                       -> InputStream ByteString     -- ^ socket read end
                       -> OutputStream Builder       -- ^ socket write end
                       -> IO ()


------------------------------------------------------------------------------
data EscapeSnap = TerminateConnection SomeException
                | EscapeHttp EscapeHttpHandler
  deriving (Typeable)

instance Exception EscapeSnap

instance Show EscapeSnap where
    show (TerminateConnection e) = "<terminated: " ++ show e ++ ">"
    show (EscapeHttp _)          = "<escape http>"


------------------------------------------------------------------------------
data Zero = PassOnProcessing
          | EarlyTermination Response
          | EscapeSnap EscapeSnap


------------------------------------------------------------------------------
newtype Snap a = Snap {
      unSnap :: forall r . (a -> SnapState -> IO r)
             -> (Zero -> SnapState -> IO r)
             -> SnapState
             -> IO r
    }


------------------------------------------------------------------------------
data SnapState = SnapState
    { _snapRequest       :: Request
    , _snapResponse      :: Response
    , _snapLogError      :: ByteString -> IO ()
    , _snapModifyTimeout :: (Int -> Int) -> IO ()
    }


------------------------------------------------------------------------------
instance Monad Snap where
    (>>=)  = snapBind
    return = snapReturn
    fail   = snapFail


------------------------------------------------------------------------------
snapBind :: Snap a -> (a -> Snap b) -> Snap b
snapBind m f = Snap $ \sk fk st -> unSnap m (\a st' -> unSnap (f a) sk fk st') fk st
{-# INLINE snapBind #-}


snapReturn :: a -> Snap a
snapReturn = pure
{-# INLINE snapReturn #-}


snapFail :: String -> Snap a
snapFail !_ = Snap $ \_ fk st -> fk PassOnProcessing st
{-# INLINE snapFail #-}


------------------------------------------------------------------------------
instance MonadIO Snap where
    liftIO m = Snap $ \sk _ st -> do x <- m
                                     sk x st


------------------------------------------------------------------------------
instance (MonadBase IO) Snap where
    liftBase = liftIO


------------------------------------------------------------------------------
instance (MonadBaseControl IO) Snap where
    newtype StM Snap a = StSnap {
          unStSnap :: StM (StateT SnapState IO) (SnapResult a)
        }

    liftBaseWith f = stateTToSnap $ liftM SnapValue $
                     liftBaseWith $ \g' -> f $ \m ->
                     liftM StSnap $ g' $ snapToStateT m
    {-# INLINE liftBaseWith #-}

    restoreM = stateTToSnap . restoreM . unStSnap
    {-# INLINE restoreM #-}

------------------------------------------------------------------------------
{-# INLINE snapToStateT #-}
snapToStateT :: Snap a -> StateT SnapState IO (SnapResult a)
snapToStateT m = StateT $ \st -> do
    unSnap m (\a st' -> return (SnapValue a, st'))
             (\z st' -> return (Zero z, st')) st


------------------------------------------------------------------------------
{-# INLINE stateTToSnap #-}
stateTToSnap :: StateT SnapState IO (SnapResult a) -> Snap a
stateTToSnap m = Snap $ \sk fk st -> do
    (a, st') <- runStateT m st
    case a of
      SnapValue x -> sk x st'
      Zero z      -> fk z st'


------------------------------------------------------------------------------
instance MonadPlus Snap where
    mzero = Snap $ \_ fk st -> fk PassOnProcessing st

    a `mplus` b =
        Snap $ \sk fk st ->
            let fk' z st' = case z of
                              PassOnProcessing -> unSnap b sk fk st'
                              _                -> fk z st'
            in unSnap a sk fk' st


------------------------------------------------------------------------------
instance Functor Snap where
    fmap f m = Snap $ \sk fk st -> unSnap m (sk . f) fk st

------------------------------------------------------------------------------
instance Applicative Snap where
    pure x  = Snap $ \sk _ st -> sk x st
    (<*>)   = ap


------------------------------------------------------------------------------
instance Alternative Snap where
    empty = mzero
    (<|>) = mplus


------------------------------------------------------------------------------
instance MonadSnap Snap where
    liftSnap = id


------------------------------------------------------------------------------
-- | The Typeable instance is here so Snap can be dynamically executed with
-- Hint.
#if __GLASGOW_HASKELL__ < 708
snapTyCon :: TyCon
#if MIN_VERSION_base(4,4,0)
snapTyCon = mkTyCon3 "snap-core" "Snap.Core" "Snap"
#else
snapTyCon = mkTyCon "Snap.Core.Snap"
#endif
{-# NOINLINE snapTyCon #-}

instance Typeable1 Snap where
    typeOf1 _ = mkTyConApp snapTyCon []
#else
deriving instance Typeable Snap
#endif

------------------------------------------------------------------------------
-- | Pass the request body stream to a consuming procedure, returning the
-- result.
--
-- If the stream you pass in here throws an exception, Snap will attempt to
-- clear the rest of the unread request body before rethrowing the exception.
-- If your iteratee used 'terminateConnection', however, Snap will give up and
-- immediately close the socket.
--
-- FIXME/TODO: reword above

runRequestBody :: MonadSnap m =>
                  (InputStream ByteString -> IO a)
               -> m a
runRequestBody proc = do
    bumpTimeout <- liftM ($ max 5) getTimeoutModifier
    req         <- getRequest
    body        <- liftIO $ Streams.throwIfTooSlow bumpTimeout 500 5 $
                            rqBody req
    run body

  where
    skip body = liftIO (Streams.skipToEof body) `catch` tooSlow

    tooSlow (e :: Streams.RateTooSlowException) =
        terminateConnection e

    run body = (liftIO $ do
        x <- proc body
        Streams.skipToEof body
        return x) `catches` handlers
      where
        handlers = [ Handler tooSlow, Handler other ]
        other (e :: SomeException) = skip body >> throwIO e


------------------------------------------------------------------------------
-- | Returns the request body as a lazy bytestring. /New in 0.6./
readRequestBody :: MonadSnap m =>
                   Word64  -- ^ size of the largest request body we're willing
                           -- to accept. If a request body longer than this is
                           -- received, a 'TooManyBytesReadException' is
                           -- thrown. See 'takeNoMoreThan'.
                -> m L.ByteString
readRequestBody sz = liftM L.fromChunks $ runRequestBody f
  where
    f str = Streams.throwIfProducesMoreThan (fromIntegral sz) str >>=
            Streams.toList


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
transformRequestBody :: (InputStream ByteString -> IO (InputStream ByteString))
                         -- ^ the 'InputStream' from the 'Request' is passed to
                         -- this function, and then the resulting 'InputStream'
                         -- is fed to the output.
                     -> Snap ()
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
finishWith :: MonadSnap m => Response -> m a
finishWith r = liftSnap $ Snap $ \_ fk st -> fk (EarlyTermination r) st
{-# INLINE finishWith #-}


------------------------------------------------------------------------------
-- | Capture the flow of control in case a handler calls 'finishWith'.
--
-- /WARNING/: in the event of a call to 'transformRequestBody' it is possible
-- to violate HTTP protocol safety when using this function. If you call
-- 'catchFinishWith' it is suggested that you do not modify the body of the
-- 'Response' which was passed to the 'finishWith' call.
catchFinishWith :: Snap a -> Snap (Either Response a)
catchFinishWith (Snap m) = Snap $ \sk fk st -> do
    let sk' v s = sk (Right v) s
    let fk' z s = case z of
                    (EarlyTermination resp) -> sk (Left resp) s
                    _                       -> fk z s
    m sk' fk' st
{-# INLINE catchFinishWith #-}


------------------------------------------------------------------------------
-- | Fails out of a 'Snap' monad action.  This is used to indicate
-- that you choose not to handle the given request within the given
-- handler.
pass :: MonadSnap m => m a
pass = empty


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only if the request's HTTP method matches
-- the given method.
method :: MonadSnap m => Method -> m a -> m a
method m action = do
    req <- getRequest
    unless (rqMethod req == m) pass
    action
{-# INLINE method #-}


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only if the request's HTTP method matches
-- one of the given methods.
methods :: MonadSnap m => [Method] -> m a -> m a
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
pathWith :: MonadSnap m
         => (ByteString -> ByteString -> Bool)
         -> ByteString
         -> m a
         -> m a
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
dir :: MonadSnap m
    => ByteString  -- ^ path component to match
    -> m a         -- ^ handler to run
    -> m a
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
path :: MonadSnap m
     => ByteString  -- ^ path to match against
     -> m a         -- ^ handler to run
     -> m a
path = pathWith (==)
{-# INLINE path #-}


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only when the first path component is
-- successfully parsed as the argument to the supplied handler function.
--
-- Note that the path segment is url-decoded prior to being passed to 'fromBS';
-- this is new as of snap-core 0.10.
pathArg :: (R.Readable a, MonadSnap m)
        => (a -> m b)
        -> m b
pathArg f = do
    req <- getRequest
    let (p,_) = S.break (=='/') (rqPathInfo req)
    p' <- maybe mzero return $ urlDecode p
    a <- R.fromBS p'
    localRequest (updateContextPath $ S.length p) (f a)


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action only when 'rqPathInfo' is empty.
ifTop :: MonadSnap m => m a -> m a
ifTop = path ""
{-# INLINE ifTop #-}


------------------------------------------------------------------------------
-- | Local Snap version of 'get'.
sget :: Snap SnapState
sget = Snap $ \sk _ st -> sk st st
{-# INLINE sget #-}


------------------------------------------------------------------------------
-- | Local Snap monad version of 'modify'.
smodify :: (SnapState -> SnapState) -> Snap ()
smodify f = Snap $ \sk _ st -> sk () (f st)
{-# INLINE smodify #-}


------------------------------------------------------------------------------
-- | Grabs the 'Request' object out of the 'Snap' monad.
getRequest :: MonadSnap m => m Request
getRequest = liftSnap $ liftM _snapRequest sget
{-# INLINE getRequest #-}


------------------------------------------------------------------------------
-- | Grabs something out of the 'Request' object, using the given projection
-- function. See 'gets'.
getsRequest :: MonadSnap m => (Request -> a) -> m a
getsRequest f = liftSnap $ liftM (f . _snapRequest) sget
{-# INLINE getsRequest #-}


------------------------------------------------------------------------------
-- | Grabs the 'Response' object out of the 'Snap' monad.
getResponse :: MonadSnap m => m Response
getResponse = liftSnap $ liftM _snapResponse sget
{-# INLINE getResponse #-}


------------------------------------------------------------------------------
-- | Grabs something out of the 'Response' object, using the given projection
-- function. See 'gets'.
getsResponse :: MonadSnap m => (Response -> a) -> m a
getsResponse f = liftSnap $ liftM (f . _snapResponse) sget
{-# INLINE getsResponse #-}


------------------------------------------------------------------------------
-- | Puts a new 'Response' object into the 'Snap' monad.
putResponse :: MonadSnap m => Response -> m ()
putResponse r = liftSnap $ smodify $ \ss -> ss { _snapResponse = r }
{-# INLINE putResponse #-}


------------------------------------------------------------------------------
-- | Puts a new 'Request' object into the 'Snap' monad.
putRequest :: MonadSnap m => Request -> m ()
putRequest r = liftSnap $ smodify $ \ss -> ss { _snapRequest = r }
{-# INLINE putRequest #-}


------------------------------------------------------------------------------
-- | Modifies the 'Request' object stored in a 'Snap' monad.
modifyRequest :: MonadSnap m => (Request -> Request) -> m ()
modifyRequest f = liftSnap $
    smodify $ \ss -> ss { _snapRequest = f $ _snapRequest ss }
{-# INLINE modifyRequest #-}


------------------------------------------------------------------------------
-- | Modifes the 'Response' object stored in a 'Snap' monad.
modifyResponse :: MonadSnap m => (Response -> Response) -> m ()
modifyResponse f = liftSnap $
     smodify $ \ss -> ss { _snapResponse = f $ _snapResponse ss }
{-# INLINE modifyResponse #-}


------------------------------------------------------------------------------
-- | Performs a redirect by setting the @Location@ header to the given target
-- URL/path and the status code to 302 in the 'Response' object stored in a
-- 'Snap' monad. Note that the target URL is not validated in any way.
-- Consider using 'redirect\'' instead, which allows you to choose the correct
-- status code.
redirect :: MonadSnap m => ByteString -> m a
redirect target = redirect' target 302
{-# INLINE redirect #-}


------------------------------------------------------------------------------
-- | Performs a redirect by setting the @Location@ header to the given target
-- URL/path and the status code (should be one of 301, 302, 303 or 307) in the
-- 'Response' object stored in a 'Snap' monad. Note that the target URL is not
-- validated in any way.
redirect' :: MonadSnap m => ByteString -> Int -> m a
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
logError :: MonadSnap m => ByteString -> m ()
logError s = liftSnap $ Snap $ \sk _ st -> do
    _snapLogError st s
    sk () st
{-# INLINE logError #-}


------------------------------------------------------------------------------
-- | Adds the output from the given enumerator to the 'Response'
-- stored in the 'Snap' monad state.
addToOutput :: MonadSnap m
            => (OutputStream Builder -> IO (OutputStream Builder))
                    -- ^ output to add
            -> m ()
addToOutput enum = modifyResponse $ modifyResponseBody (c enum)
  where
    c a b = \out -> b out >>= a

------------------------------------------------------------------------------
-- | Adds the given 'Builder' to the body of the 'Response' stored in the
-- | 'Snap' monad state.
writeBuilder :: MonadSnap m => Builder -> m ()
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
writeBS :: MonadSnap m => ByteString -> m ()
writeBS s = writeBuilder $ fromByteString s


------------------------------------------------------------------------------
-- | Adds the given lazy 'L.ByteString' to the body of the 'Response' stored
-- in the 'Snap' monad state.
--
-- Warning: This function is intentionally non-strict. If any pure
-- exceptions are raised by the expression creating the 'ByteString',
-- the exception won't actually be raised within the Snap handler.
writeLBS :: MonadSnap m => L.ByteString -> m ()
writeLBS s = writeBuilder $ fromLazyByteString s


------------------------------------------------------------------------------
-- | Adds the given strict 'T.Text' to the body of the 'Response' stored in
-- the 'Snap' monad state.
--
-- Warning: This function is intentionally non-strict. If any pure
-- exceptions are raised by the expression creating the 'ByteString',
-- the exception won't actually be raised within the Snap handler.
writeText :: MonadSnap m => T.Text -> m ()
writeText s = writeBuilder $ fromText s


------------------------------------------------------------------------------
-- | Adds the given lazy 'LT.Text' to the body of the 'Response' stored in the
-- 'Snap' monad state.
--
-- Warning: This function is intentionally non-strict. If any pure
-- exceptions are raised by the expression creating the 'ByteString',
-- the exception won't actually be raised within the Snap handler.
writeLazyText :: MonadSnap m => LT.Text -> m ()
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
sendFile :: (MonadSnap m) => FilePath -> m ()
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
sendFilePartial :: (MonadSnap m) => FilePath -> (Word64, Word64) -> m ()
sendFilePartial f rng = modifyResponse $ \r ->
                        r { rspBody = SendFile f (Just rng) }


------------------------------------------------------------------------------
-- | Runs a 'Snap' action with a locally-modified 'Request' state
-- object. The 'Request' object in the Snap monad state after the call
-- to localRequest will be unchanged.
localRequest :: MonadSnap m => (Request -> Request) -> m a -> m a
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
withRequest :: MonadSnap m => (Request -> m a) -> m a
withRequest = (getRequest >>=)
{-# INLINE withRequest #-}


------------------------------------------------------------------------------
-- | Fetches the 'Response' from state and hands it to the given action.
withResponse :: MonadSnap m => (Response -> m a) -> m a
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
ipHeaderFilter :: MonadSnap m => m ()
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
ipHeaderFilter' :: MonadSnap m => CI ByteString -> m ()
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
bracketSnap :: IO a -> (a -> IO b) -> (a -> Snap c) -> Snap c
bracketSnap before after thing = mask $ \restore ->
                                 stateTToSnap $ do
    a <- liftIO before
    let after' = liftIO $ after a
    r <- snapToStateT (restore $ thing a) `onException` after'
    _ <- after'
    return r


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
terminateConnection :: (Exception e, MonadSnap m) => e -> m a
terminateConnection e =
    liftSnap $ Snap $ \_ fk -> fk $ EscapeSnap $ TerminateConnection
                                  $ SomeException e


------------------------------------------------------------------------------
-- | Terminate the HTTP session and hand control to some external handler,
-- escaping all further HTTP traffic.
--
-- The external handler takes two arguments: a function to modify the thread's
-- timeout, and a write end to the socket.
escapeHttp :: MonadSnap m =>
              EscapeHttpHandler
           -> m ()
escapeHttp h = liftSnap $ Snap $ \_ fk st -> fk (EscapeSnap $ EscapeHttp h) st


------------------------------------------------------------------------------
-- | Runs a 'Snap' monad action.
runSnap :: Snap a
        -> (ByteString -> IO ())
        -> ((Int -> Int) -> IO ())
        -> Request
        -> IO (Request, Response)
runSnap (Snap m) logerr timeoutAction req =
    m ok diediedie ss
  where
    ok _ st = do
        let req' = _snapRequest st
        let resp = _snapResponse st
        resp' <- liftIO $ fixupResponse req' resp
        return (req', resp')

    diediedie z !st = do
        rsp <- case z of
                 PassOnProcessing     -> return fourohfour
                 (EarlyTermination x) -> return x
                 (EscapeSnap e)       -> throwIO e
        return (_snapRequest st, rsp)

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
    dresp = emptyResponse

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
--
{-# INLINE fixupResponse #-}
fixupResponse :: Request -> Response -> IO Response
fixupResponse req rsp = {-# SCC "fixupResponse" #-} do
    rsp' <- case rspBody rsp of
              (Stream _)                -> return rsp
              (SendFile f Nothing)      -> setFileSize f rsp
              (SendFile _ (Just (s,e))) -> return $! setContentLength (e-s) rsp
    let !cl = if noBody then Nothing else rspContentLength rsp'
    let rsp'' = if noBody
                  then rsp' { rspBody          = Stream $ return . id
                            , rspContentLength = Nothing
                            }
                  else rsp'
    return $! updateHeaders (H.fromList . addCL cl . fixup . H.toList) rsp''

  where
    --------------------------------------------------------------------------
    addCL Nothing xs   = xs
    addCL (Just cl) xs = ("content-length", word64ToByteString cl):xs

    --------------------------------------------------------------------------
    setFileSize :: FilePath -> Response -> IO Response
    setFileSize fp r = {-# SCC "setFileSize" #-} do
        fs <- liftM fromIntegral $ getFileSize fp
        return $! r { rspContentLength = Just fs }

    ------------------------------------------------------------------------------
    getFileSize :: FilePath -> IO FileOffset
    getFileSize fp = liftM fileSize $ getFileStatus fp

    code   = rspStatus rsp
    noBody = code == 204 || code == 304 || rqMethod req == HEAD

    ------------------------------------------------------------------------------
    fixup [] = []
    fixup (("date",_):xs)           = fixup xs
    fixup (("content-length",_):xs) = fixup xs
    fixup (x@("transfer-encoding",_):xs) = if noBody
                                             then fixup xs
                                             else x : fixup xs
    fixup (x:xs) = x : fixup xs


------------------------------------------------------------------------------
-- This number code stolen and massaged from Bryan's blog post:
-- http://www.serpentine.com/blog/2013/03/20/whats-good-for-c-is-good-for-haskell/

{-# INLINE countDigits #-}
countDigits :: Word64 -> Int
countDigits v0 = go 1 v0
  where go !k v
           | v < 10    = k
           | v < 100   = k + 1
           | v < 1000  = k + 2
           | v < 10000 = k + 3
           | otherwise = go (k+4) (v `quot` 10000)


------------------------------------------------------------------------------
{-# INLINE word64ToByteString #-}
word64ToByteString :: Word64 -> ByteString
word64ToByteString d =
    S.inlinePerformIO $
    if d < 10
       then S.create 1 $ \p -> poke p (i2w d)
       else let !n = countDigits d
            in S.create n $ posDecimal n d


{-# INLINE posDecimal #-}
posDecimal :: Int -> Word64 -> Ptr Word8 -> IO ()
posDecimal !n0 !v0 !op0 = go n0 (plusPtr op0 (n0-1)) v0
  where go !n !op !v
          | n == 1 = poke op $! i2w v
          | otherwise = do
              let (!v', !d) = divMod v 10
              poke op $! i2w d
              go (n-1) (plusPtr op (-1)) v'


{-# INLINE i2w #-}
i2w :: Word64 -> Word8
i2w v = 48 + fromIntegral v


------------------------------------------------------------------------------
evalSnap :: Snap a
         -> (ByteString -> IO ())
         -> ((Int -> Int) -> IO ())
         -> Request
         -> IO a
evalSnap (Snap m) logerr timeoutAction req =
    m (\v _ -> return v) diediedie ss
  where
    diediedie z _ = case z of
      PassOnProcessing     -> throwIO $ NoHandlerException "pass"
      (EarlyTermination _) -> throwIO $ ErrorCall "no value"
      (EscapeSnap e)       -> throwIO e

    dresp = emptyResponse
    ss = SnapState req dresp logerr timeoutAction
{-# INLINE evalSnap #-}


------------------------------------------------------------------------------
getParamFrom :: MonadSnap m =>
                (ByteString -> Request -> Maybe [ByteString])
             -> ByteString
             -> m (Maybe ByteString)
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
getParam :: MonadSnap m
         => ByteString          -- ^ parameter name to look up
         -> m (Maybe ByteString)
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
getPostParam :: MonadSnap m
             => ByteString          -- ^ parameter name to look up
             -> m (Maybe ByteString)
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
getQueryParam :: MonadSnap m
              => ByteString          -- ^ parameter name to look up
              -> m (Maybe ByteString)
getQueryParam = getParamFrom rqQueryParam
{-# INLINE getQueryParam #-}


------------------------------------------------------------------------------
-- | See 'rqParams'. Convenience function to return 'Params' from the
-- 'Request' inside of a 'MonadSnap' instance.
getParams :: MonadSnap m => m Params
getParams = getRequest >>= return . rqParams


------------------------------------------------------------------------------
-- | See 'rqParams'. Convenience function to return 'Params' from the
-- 'Request' inside of a 'MonadSnap' instance.
getPostParams :: MonadSnap m => m Params
getPostParams = getRequest >>= return . rqPostParams


------------------------------------------------------------------------------
-- | See 'rqParams'. Convenience function to return 'Params' from the
-- 'Request' inside of a 'MonadSnap' instance.
getQueryParams :: MonadSnap m => m Params
getQueryParams = getRequest >>= return . rqQueryParams


------------------------------------------------------------------------------
-- | Gets the HTTP 'Cookie' with the specified name.
getCookie :: MonadSnap m
          => ByteString
          -> m (Maybe Cookie)
getCookie name = withRequest $
    return . listToMaybe . filter (\c -> cookieName c == name) . rqCookies


------------------------------------------------------------------------------
-- | Gets the HTTP 'Cookie' with the specified name and decodes it.  If the
-- decoding fails, the handler calls pass.
readCookie :: (MonadSnap m, R.Readable a)
           => ByteString
           -> m a
readCookie name = maybe pass (R.fromBS . cookieValue) =<< getCookie name


------------------------------------------------------------------------------
-- | Expire the given 'Cookie' in client's browser.
expireCookie :: (MonadSnap m)
             => ByteString
             -- ^ Cookie name
             -> Maybe ByteString
             -- ^ Cookie domain
             -> m ()
expireCookie nm dm = do
  let old = UTCTime (ModifiedJulianDay 0) 0
  modifyResponse $ addResponseCookie
                 $ Cookie nm "" (Just old) Nothing dm False False


------------------------------------------------------------------------------
-- | Causes the handler thread to be killed @n@ seconds from now.
setTimeout :: MonadSnap m => Int -> m ()
setTimeout = modifyTimeout . const


------------------------------------------------------------------------------
-- | Causes the handler thread to be killed at least @n@ seconds from now.
extendTimeout :: MonadSnap m => Int -> m ()
extendTimeout = modifyTimeout . max


------------------------------------------------------------------------------
-- | Modifies the amount of time remaining before the request times out.
modifyTimeout :: MonadSnap m => (Int -> Int) -> m ()
modifyTimeout f = do
    m <- getTimeoutModifier
    liftIO $ m f


------------------------------------------------------------------------------
-- | Returns an 'IO' action which you can use to modify the timeout value.
getTimeoutModifier :: MonadSnap m => m ((Int -> Int) -> IO ())
getTimeoutModifier = liftSnap $ liftM _snapModifyTimeout sget
