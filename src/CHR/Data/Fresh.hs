-------------------------------------------------------------------------------------------
--- Freshness of something
-------------------------------------------------------------------------------------------

module CHR.Data.Fresh
  ( -- MonadFresh(..)
    Fresh(..)
  )
  where

{-
class Monad m => MonadFresh f m where
  -- | Fresh single 'f'
  fresh :: m f
  fresh = freshInf

  -- | Fresh infinite range of 'f'
  freshInf :: m f
  freshInf = fresh
-}

class Fresh fs f where
  -- | Fresh single 'f', and modifier 'upd' for freshly created value
  freshWith :: Maybe f -> fs -> (f,fs)
  freshWith = freshInfWith

  -- | Fresh single 'f'
  fresh :: fs -> (f,fs)
  fresh = freshWith Nothing

  -- | Fresh infinite range of 'f', and modifier 'upd' for freshly created value
  freshInfWith :: Maybe f -> fs -> (f,fs)
  freshInfWith = freshWith

  -- | Fresh infinite range of 'f'
  freshInf :: fs -> (f,fs)
  freshInf = freshInfWith Nothing

instance Fresh Int Int where
  freshWith _ i = (i, i+1)

instance Fresh Int String where
  freshWith orig i = (maybe f (\o -> f ++ "_" ++ o) orig, i+1)
    where f = "$" ++ show i
