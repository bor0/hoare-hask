module PrettyPrinter where

{- Pretty printer -}
class Pretty a where
  pr :: a -> String

instance Pretty Integer where
  pr = show

instance Pretty Bool where
  pr = show
