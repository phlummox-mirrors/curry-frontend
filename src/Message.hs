-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- Message - A library for dealing with messages
--                
-- November 2005,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module Message where

import Position


-------------------------------------------------------------------------------

-- Generates a new message
message :: a -> String -> Message a
message mtype msg = Message mtype msg

-- Returns the number of messages which has the same type 
countMessages :: Eq a => a -> [Message a] -> Int
countMessages mtype msgs = length (filter (hasType mtype) msgs)

-- Shows a message
showMessage :: (a -> String) -> Message a -> String
showMessage showType (Message mtype msg)
   = showType mtype ++ msg


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

-- Data type for representing compiler messages of an arbitrary type
--
--      Message <message type> <message>
--
data Message a = Message a String

-------------------------------------------------------------------------------

--
hasType :: Eq a => a -> Message a -> Bool
hasType mtype (Message mtype' _) = mtype == mtype'


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------