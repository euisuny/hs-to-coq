{-# LINE 1 "Options.hsc" #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}


#include "HsNetDef.h"

module Network.Socket.Options (
    SocketOption(..)
  , isSupportedSocketOption
  , getSocketType
  , getSocketOption
  , setSocketOption
  , c_getsockopt
  , c_setsockopt
  ) where

import Foreign.Marshal.Alloc (alloca)
import Foreign.Marshal.Utils (with)

import Network.Socket.Imports
import Network.Socket.Internal
import Network.Socket.Types

-----------------------------------------------------------------------------
-- Socket Properties

-- | Socket options for use with 'setSocketOption' and 'getSocketOption'.
--
-- The existence of a constructor does not imply that the relevant option
-- is supported on your system: see 'isSupportedSocketOption'
data SocketOption
    = Debug         -- ^ SO_DEBUG
    | ReuseAddr     -- ^ SO_REUSEADDR
    | Type          -- ^ SO_TYPE
    | SoError       -- ^ SO_ERROR
    | DontRoute     -- ^ SO_DONTROUTE
    | Broadcast     -- ^ SO_BROADCAST
    | SendBuffer    -- ^ SO_SNDBUF
    | RecvBuffer    -- ^ SO_RCVBUF
    | KeepAlive     -- ^ SO_KEEPALIVE
    | OOBInline     -- ^ SO_OOBINLINE
    | TimeToLive    -- ^ IP_TTL
    | MaxSegment    -- ^ TCP_MAXSEG
    | NoDelay       -- ^ TCP_NODELAY
    | Cork          -- ^ TCP_CORK
    | Linger        -- ^ SO_LINGER: timeout in seconds, 0 means disabling/disabled.
    | ReusePort     -- ^ SO_REUSEPORT
    | RecvLowWater  -- ^ SO_RCVLOWAT
    | SendLowWater  -- ^ SO_SNDLOWAT
    | RecvTimeOut   -- ^ SO_RCVTIMEO: this does not work at this moment.
    | SendTimeOut   -- ^ SO_SNDTIMEO: this does not work at this moment.
    | UseLoopBack   -- ^ SO_USELOOPBACK
    | UserTimeout   -- ^ TCP_USER_TIMEOUT
    | IPv6Only      -- ^ IPV6_V6ONLY: don't use this on OpenBSD.
    | CustomSockOpt (CInt, CInt)
    deriving (Show, Typeable)

-- | Does the 'SocketOption' exist on this system?
isSupportedSocketOption :: SocketOption -> Bool
isSupportedSocketOption = isJust . packSocketOption

-- | Get the 'SocketType' of an active socket.
--
--   Since: 3.0.1.0
getSocketType :: Socket -> IO SocketType
getSocketType s = (fromMaybe NoSocketType . unpackSocketType . fromIntegral)
                    <$> getSocketOption s Type

-- | For a socket option, return Just (level, value) where level is the
-- corresponding C option level constant (e.g. SOL_SOCKET) and value is
-- the option constant itself (e.g. SO_DEBUG)
-- If either constant does not exist, return Nothing.
packSocketOption :: SocketOption -> Maybe (CInt, CInt)
packSocketOption so =
  -- The Just here is a hack to disable GHC's overlapping pattern detection:
  -- the problem is if all constants are present, the fallback pattern is
  -- redundant, but if they aren't then it isn't. Hence we introduce an
  -- extra pattern (Nothing) that can't possibly happen, so that the
  -- fallback is always (in principle) necessary.
  -- I feel a little bad for including this, but such are the sacrifices we
  -- make while working with CPP - excluding the fallback pattern correctly
  -- would be a serious nuisance.
  -- (NB: comments elsewhere in this file refer to this one)
  case Just so of

{-# LINE 86 "Options.hsc" #-}

{-# LINE 87 "Options.hsc" #-}
    Just Debug         -> Just ((65535), (1))
{-# LINE 88 "Options.hsc" #-}

{-# LINE 89 "Options.hsc" #-}

{-# LINE 90 "Options.hsc" #-}
    Just ReuseAddr     -> Just ((65535), (4))
{-# LINE 91 "Options.hsc" #-}

{-# LINE 92 "Options.hsc" #-}

{-# LINE 93 "Options.hsc" #-}
    Just Type          -> Just ((65535), (4104))
{-# LINE 94 "Options.hsc" #-}

{-# LINE 95 "Options.hsc" #-}

{-# LINE 96 "Options.hsc" #-}
    Just SoError       -> Just ((65535), (4103))
{-# LINE 97 "Options.hsc" #-}

{-# LINE 98 "Options.hsc" #-}

{-# LINE 99 "Options.hsc" #-}
    Just DontRoute     -> Just ((65535), (16))
{-# LINE 100 "Options.hsc" #-}

{-# LINE 101 "Options.hsc" #-}

{-# LINE 102 "Options.hsc" #-}
    Just Broadcast     -> Just ((65535), (32))
{-# LINE 103 "Options.hsc" #-}

{-# LINE 104 "Options.hsc" #-}

{-# LINE 105 "Options.hsc" #-}
    Just SendBuffer    -> Just ((65535), (4097))
{-# LINE 106 "Options.hsc" #-}

{-# LINE 107 "Options.hsc" #-}

{-# LINE 108 "Options.hsc" #-}
    Just RecvBuffer    -> Just ((65535), (4098))
{-# LINE 109 "Options.hsc" #-}

{-# LINE 110 "Options.hsc" #-}

{-# LINE 111 "Options.hsc" #-}
    Just KeepAlive     -> Just ((65535), (8))
{-# LINE 112 "Options.hsc" #-}

{-# LINE 113 "Options.hsc" #-}

{-# LINE 114 "Options.hsc" #-}
    Just OOBInline     -> Just ((65535), (256))
{-# LINE 115 "Options.hsc" #-}

{-# LINE 116 "Options.hsc" #-}

{-# LINE 117 "Options.hsc" #-}
    Just Linger        -> Just ((65535), (128))
{-# LINE 118 "Options.hsc" #-}

{-# LINE 119 "Options.hsc" #-}

{-# LINE 120 "Options.hsc" #-}
    Just ReusePort     -> Just ((65535), (512))
{-# LINE 121 "Options.hsc" #-}

{-# LINE 122 "Options.hsc" #-}

{-# LINE 123 "Options.hsc" #-}
    Just RecvLowWater  -> Just ((65535), (4100))
{-# LINE 124 "Options.hsc" #-}

{-# LINE 125 "Options.hsc" #-}

{-# LINE 126 "Options.hsc" #-}
    Just SendLowWater  -> Just ((65535), (4099))
{-# LINE 127 "Options.hsc" #-}

{-# LINE 128 "Options.hsc" #-}

{-# LINE 129 "Options.hsc" #-}
    Just RecvTimeOut   -> Just ((65535), (4102))
{-# LINE 130 "Options.hsc" #-}

{-# LINE 131 "Options.hsc" #-}

{-# LINE 132 "Options.hsc" #-}
    Just SendTimeOut   -> Just ((65535), (4101))
{-# LINE 133 "Options.hsc" #-}

{-# LINE 134 "Options.hsc" #-}

{-# LINE 135 "Options.hsc" #-}
    Just UseLoopBack   -> Just ((65535), (64))
{-# LINE 136 "Options.hsc" #-}

{-# LINE 137 "Options.hsc" #-}

{-# LINE 138 "Options.hsc" #-}

{-# LINE 139 "Options.hsc" #-}

{-# LINE 140 "Options.hsc" #-}
    Just TimeToLive    -> Just ((0), (4))
{-# LINE 141 "Options.hsc" #-}

{-# LINE 142 "Options.hsc" #-}

{-# LINE 143 "Options.hsc" #-}

{-# LINE 144 "Options.hsc" #-}

{-# LINE 145 "Options.hsc" #-}
    Just MaxSegment    -> Just ((6), (2))
{-# LINE 146 "Options.hsc" #-}

{-# LINE 147 "Options.hsc" #-}

{-# LINE 148 "Options.hsc" #-}
    Just NoDelay       -> Just ((6), (1))
{-# LINE 149 "Options.hsc" #-}

{-# LINE 150 "Options.hsc" #-}

{-# LINE 153 "Options.hsc" #-}

{-# LINE 156 "Options.hsc" #-}

{-# LINE 157 "Options.hsc" #-}

{-# LINE 158 "Options.hsc" #-}

{-# LINE 159 "Options.hsc" #-}
    Just IPv6Only      -> Just ((41), (27))
{-# LINE 160 "Options.hsc" #-}

{-# LINE 161 "Options.hsc" #-}

{-# LINE 162 "Options.hsc" #-}
    Just (CustomSockOpt opt) -> Just opt
    _             -> Nothing

-- | Return the option level and option value if they exist,
-- otherwise throw an error that begins "Network.Socket." ++ the String
-- parameter
packSocketOption' :: String -> SocketOption -> IO (CInt, CInt)
packSocketOption' caller so = maybe err return (packSocketOption so)
 where
  err = ioError . userError . concat $ ["Network.Socket.", caller,
    ": socket option ", show so, " unsupported on this system"]


{-# LINE 175 "Options.hsc" #-}
data StructLinger = StructLinger CInt CInt

instance Storable StructLinger where
    sizeOf _ = (8)
{-# LINE 179 "Options.hsc" #-}
    alignment _ = alignment (undefined :: CInt)

    peek p = do
        onoff  <- ((\hsc_ptr -> peekByteOff hsc_ptr 0)) p
{-# LINE 183 "Options.hsc" #-}
        linger <- ((\hsc_ptr -> peekByteOff hsc_ptr 4)) p
{-# LINE 184 "Options.hsc" #-}
        return $ StructLinger onoff linger

    poke p (StructLinger onoff linger) = do
        ((\hsc_ptr -> pokeByteOff hsc_ptr 0))  p onoff
{-# LINE 188 "Options.hsc" #-}
        ((\hsc_ptr -> pokeByteOff hsc_ptr 4)) p linger
{-# LINE 189 "Options.hsc" #-}

{-# LINE 190 "Options.hsc" #-}

-- | Set a socket option that expects an Int value.
-- There is currently no API to set e.g. the timeval socket options
setSocketOption :: Socket
                -> SocketOption -- Option Name
                -> Int          -- Option Value
                -> IO ()

{-# LINE 198 "Options.hsc" #-}
setSocketOption s Linger v = do
   (level, opt) <- packSocketOption' "setSocketOption" Linger
   let arg = if v == 0 then StructLinger 0 0 else StructLinger 1 (fromIntegral v)
   with arg $ \ptr_arg -> void $ do
     let ptr = ptr_arg :: Ptr StructLinger
         sz = fromIntegral $ sizeOf (undefined :: StructLinger)
     withFdSocket s $ \fd ->
       throwSocketErrorIfMinus1_ "Network.Socket.setSocketOption" $
         c_setsockopt fd level opt ptr sz

{-# LINE 208 "Options.hsc" #-}
setSocketOption s so v = do
   (level, opt) <- packSocketOption' "setSocketOption" so
   with (fromIntegral v) $ \ptr_v -> void $ do
     let ptr = ptr_v :: Ptr CInt
         sz  = fromIntegral $ sizeOf (undefined :: CInt)
     withFdSocket s $ \fd ->
       throwSocketErrorIfMinus1_ "Network.Socket.setSocketOption" $
         c_setsockopt fd level opt ptr sz

-- | Get a socket option that gives an Int value.
-- There is currently no API to get e.g. the timeval socket options
getSocketOption :: Socket
                -> SocketOption  -- Option Name
                -> IO Int        -- Option Value

{-# LINE 223 "Options.hsc" #-}
getSocketOption s Linger = do
   (level, opt) <- packSocketOption' "getSocketOption" Linger
   alloca $ \ptr_v -> do
     let ptr = ptr_v :: Ptr StructLinger
         sz = fromIntegral $ sizeOf (undefined :: StructLinger)
     withFdSocket s $ \fd -> with sz $ \ptr_sz -> do
       throwSocketErrorIfMinus1Retry_ "Network.Socket.getSocketOption" $
         c_getsockopt fd level opt ptr ptr_sz
       StructLinger onoff linger <- peek ptr
       return $ fromIntegral $ if onoff == 0 then 0 else linger

{-# LINE 234 "Options.hsc" #-}
getSocketOption s so = do
   (level, opt) <- packSocketOption' "getSocketOption" so
   alloca $ \ptr_v -> do
     let ptr = ptr_v :: Ptr CInt
         sz = fromIntegral $ sizeOf (undefined :: CInt)
     withFdSocket s $ \fd -> with sz $ \ptr_sz -> do
       throwSocketErrorIfMinus1Retry_ "Network.Socket.getSocketOption" $
         c_getsockopt fd level opt ptr ptr_sz
       fromIntegral <$> peek ptr

foreign import CALLCONV unsafe "getsockopt"
  c_getsockopt :: CInt -> CInt -> CInt -> Ptr a -> Ptr CInt -> IO CInt
foreign import CALLCONV unsafe "setsockopt"
  c_setsockopt :: CInt -> CInt -> CInt -> Ptr a -> CInt -> IO CInt
