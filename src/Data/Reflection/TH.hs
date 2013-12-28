module Data.Reflection.TH where
import Haskell.Language.TH

{-
instance Reifies s (Def Show a) => Show (Lift Show a s) where
  show a = show_ (reflect a) (lower a)

instance ReifiableConstraint Show where
  data Def Show a = Show { show_ :: a -> String }
  reifiedIns = Sub Dict
-}

withClassD :: String 
           -> ((Cxt, Name, [TyVarBndr], [FunDep], [Dec]) -> a) 
           -> Dec 
           -> a
withClassD errMsg f = \case 
   ClassD a b c d e -> f (a, b, c, d, e)
   _ -> error errMsg
   
withSigD :: String 
         -> ((Name, Type) -> a)
         -> Dec 
         -> a
withSigD errMsg f = \case
   SigD n typ -> f (n, typ)
   _ -> error errMsg
  
getArgumentTypes :: Type -> [Type]
getArgumentTypes typs = flip unfoldr typs $ \case
   AppT _ x -> Just ((), x)
   _        -> Nothing
         
countVariables :: Type -> Int
countVariables = length . getArgumentTypes
   
getOutputType :: Type -> Type
getOutputType = last . getArgumentTypes
         
makeReifiesDec ::  Name -> Dec -> Q Dec
makeReifiesDec sVar = withSigN "makeReifiesDec" $ \(name, typ) -> do
      let varCount = countVariables typ
      varNames <- replicateM varCount newName
      let ps       = map VarP varNames
          getFunc  = (mkName . (<> "_") . nameBase $ name) 
              `AppE` ((ConE 'Proxy ) `SigE` (ConT ''Proxy `AppT` sVar))
      
          lowers   = map (AppT 'lower . VarE) varNames 
          funct    = foldl1 AppT $ getFunc : lowers
          
          body     = AppT fmaps funct
      return $ FunD name [Clause ps body []]

mkReifiesInstance :: Dec -> Q Dec 
mkReifiesInstance dec = "mkReifiesInstance expects a ClassD" $ 
   \(cxt, name, [PlainTV s, PlainTV a], _, decs) -> do
      s <- newName "s"
      a <- newName "a"
      defType = ConT ''Def `AppT` ConT name `AppT` VarT a
      cxt = ClassP ''Reifies [VarT s, defType]
      
      newDecs = map (makeReifiesDec s) decs
      
      return $ InstanceD [cxt] typ decs 