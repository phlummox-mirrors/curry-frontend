

class A a => B a where

class B a => A a where


class Cycles.C a => D a where

class Cycles.D a => C a where


class Cycles.E a => F a where

class F a => E a where

