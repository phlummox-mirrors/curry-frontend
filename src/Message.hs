-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--
-- Message - A library for dealing with compiler messages
--
-- Note: This module overwrites the functions declared in "Message"
--                
-- January 2006,
-- Martin Engelke (men@informatik.uni-kiel.de)
--
module Message where

import Position


-------------------------------------------------------------------------------

-- Type for representing compiler messages (currently errors and warnings)
data Message = Message MessageType Position String

-- Data type for representing available compiler message types
data MessageType = Warning  | Error deriving Eq


-- An instance of Show for converting messages to readable strings
instance Show Message where
 show (Message Warning pos msg) = showMessage "Warning" pos msg
 show (Message Error   pos msg) = showMessage "ERROR" pos msg


-------------------------------------------------------------------------------

--
message :: MessageType -> Position -> String -> Message
message = Message 

--
countMessages :: MessageType -> [Message] -> Int
countMessages mtype msgs = length (filter (((==) mtype) . messageType) msgs)

--
messageType :: Message -> MessageType
messageType (Message mtype _ _) = mtype


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--
showMessage :: String -> Position -> String -> String
showMessage what pos msg
   | pos == first "" = what ++ ": " ++ msg
   | otherwise       = what ++ ": " ++ show pos ++ ": " ++ msg


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------