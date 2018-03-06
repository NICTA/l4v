--
-- Copyright 2014, General Dynamics C4 Systems
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(GD_GPL)
--

{-# LANGUAGE EmptyDataDecls, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}

module SEL4.Machine.Hardware.ARM.KZM where

import SEL4.Machine.RegisterSet
import Foreign.Ptr
import Data.Bits
import Data.Word(Word8, Word64)
import Data.Ix
import SEL4.Machine.Hardware.ARM.Callbacks


newtype IRQ = IRQ Word8
    deriving (Enum, Ord, Ix, Eq, Show)

instance Bounded IRQ where
    minBound = IRQ 0
    maxBound = IRQ 31

kernelBase :: VPtr
kernelBase = VPtr 0xf0000000

physBase = 0x80000000
physMappingOffset = 0xf0000000 - physBase

ptrFromPAddr :: PAddr -> PPtr a
ptrFromPAddr (PAddr addr) = PPtr $ addr + physMappingOffset

addrFromPPtr :: PPtr a -> PAddr
addrFromPPtr (PPtr ptr) = PAddr $ ptr - physMappingOffset

pageColourBits :: Int
pageColourBits = 0 -- qemu has no cache

getMemoryRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getMemoryRegions _ = return [(0x80000000, 0x80000000 + (0x8 `shiftL` 24))]

getDeviceRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getDeviceRegions _ = return devices
    where devices = [
            (0x53f98000, 0x53f99000) -- second SP804; kernel uses first
            ]

timerPPtr = PPtr 0xfff00000
timerAddr = PAddr 0x53f94000
timerIRQ = IRQ 28

avicPPtr = PPtr 0xfff01000
avicAddr = PAddr 0x68000000

getKernelDevices :: Ptr CallbackData -> IO [(PAddr, PPtr Word)]
getKernelDevices _ = return devices
    where devices = [
            (timerAddr, timerPPtr), -- kernel timer
            (avicAddr, avicPPtr) -- interrupt controller
            ]

maskInterrupt :: Ptr CallbackData -> Bool -> IRQ -> IO ()
maskInterrupt env mask (IRQ irq) = do
    let value = fromIntegral irq
    offset <- return $ if (mask == True) then 0xc else 0x8
    storeWordCallback env (avicAddr + offset) value

-- We don't need to acknowledge interrupts explicitly because we don't use
-- the vectored interrupt controller.
ackInterrupt :: Ptr CallbackData -> IRQ -> IO ()
ackInterrupt _ _ = return ()

foreign import ccall unsafe "qemu_run_devices"
    runDevicesCallback :: Ptr CallbackData -> IO ()

interruptCallback :: Ptr CallbackData -> IO (Maybe IRQ)
interruptCallback env = do
    -- No need to call back to the simulator here; we just check the PIC's
    -- active interrupt register. This will probably work for real ARMs too,
    -- as long as we're not using vectored interrupts
    active <- loadWordCallback env (avicAddr + 64)
    return $ if active == 0xFFFF0000
        then Nothing
        else (Just $ IRQ $ fromIntegral (active `shiftR` 16))

getActiveIRQ :: Ptr CallbackData -> IO (Maybe IRQ)
getActiveIRQ env = do
    runDevicesCallback env
    interruptCallback env

-- 1kHz tick; qemu's SP804s always run at 1MHz
timerFreq :: Word
timerFreq = 100

timerLimit :: Word
timerLimit = 1000000 `div` timerFreq

setDeadline :: Ptr CallbackData -> Word64 -> IO ()
setDeadline _ _ = undefined

initIRQController :: Ptr CallbackData -> IO ()
initIRQController env = runDevicesCallback env

resetTimer :: Ptr CallbackData -> IO ()
resetTimer env = storeWordCallback env (timerAddr+0x4) 1

isbCallback :: Ptr CallbackData -> IO ()
isbCallback _ = return ()

dsbCallback :: Ptr CallbackData -> IO ()
dsbCallback _ = return ()

dmbCallback :: Ptr CallbackData -> IO ()
dmbCallback _ = return ()

cacheCleanByVACallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanByVACallback _cptr _mva _pa = return ()

cacheCleanByVA_PoUCallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanByVA_PoUCallback _cptr _mva _pa = return ()

cacheInvalidateByVACallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheInvalidateByVACallback _cptr _mva _pa = return ()

cacheInvalidateByVA_ICallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheInvalidateByVA_ICallback _cptr _mva _pa = return ()

cacheInvalidate_I_PoUCallback :: Ptr CallbackData -> IO ()
cacheInvalidate_I_PoUCallback _ = return ()

cacheCleanInvalidateByVACallback ::
    Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanInvalidateByVACallback _cptr _mva _pa = return ()

branchFlushCallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
branchFlushCallback _cptr _mva _pa = return ()

cacheClean_D_PoUCallback :: Ptr CallbackData -> IO ()
cacheClean_D_PoUCallback _ = return ()

cacheCleanInvalidate_D_PoCCallback :: Ptr CallbackData -> IO ()
cacheCleanInvalidate_D_PoCCallback _ = return ()

cacheCleanInvalidate_D_PoUCallback :: Ptr CallbackData -> IO ()
cacheCleanInvalidate_D_PoUCallback _ = return ()

cacheCleanInvalidateL2RangeCallback ::
    Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheCleanInvalidateL2RangeCallback _ _ _ = return ()

cacheInvalidateL2RangeCallback :: Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheInvalidateL2RangeCallback _ _ _ = return ()

cacheCleanL2RangeCallback :: Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheCleanL2RangeCallback _ _ _ = return ()

-- For the ARM1136
cacheLine :: Int
cacheLine = 32

cacheLineBits :: Int
cacheLineBits = 5
