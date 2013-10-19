
import TestDeriving1
import TestDeriving2
import TestDerivingBounded
import TestDerivingEnum
import TestEnumerations
import TestList
import TestPrelude
import TestShow

allTests = [ TestDeriving1.allCorrect
           , TestDeriving2.allCorrect
           , TestDerivingBounded.allCorrect
           , TestDerivingEnum.allCorrect
           , TestEnumerations.allCorrect
           , TestList.allCorrect
           , TestPrelude.allCorrect
           , TestShow.allCorrect
           ]

allCorrect = and allTests