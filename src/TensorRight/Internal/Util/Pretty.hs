{-# LANGUAGE OverloadedStrings #-}

module TensorRight.Internal.Util.Pretty
  ( encloseList,
    groupedEnclose,
    condEnclose,
    prettyWithConstructor,
    gprettyParen,
    printTitle,
    printSuccess,
    printFailure,
    printWarning,
  )
where

import Prettyprinter (Doc, align, cat, flatAlt, group, nest, vcat, vsep)

encloseList :: Doc ann -> Doc ann -> Doc ann -> [Doc ann] -> Doc ann
encloseList l r s ds = case ds of
  [] -> l <> r
  [d] -> cat [nest 2 $ vcat [l, d], r]
  _ ->
    group $
      vcat [nest 2 $ vcat [l, vcat $ map (<> sep) (init ds), last ds], r]
  where
    sep = flatAlt s (s <> " ")

groupedEnclose :: Doc ann -> Doc ann -> Doc ann -> Doc ann
groupedEnclose l r d = group $ align $ vcat [l <> flatAlt " " "" <> d, r]

condEnclose :: Bool -> Doc ann -> Doc ann -> Doc ann -> Doc ann
condEnclose b = if b then groupedEnclose else const $ const id

gprettyParen :: Bool -> Doc ann -> Doc ann
gprettyParen b = condEnclose b "(" ")"

prettyWithConstructor :: Int -> Doc ann -> [Doc ann] -> Doc ann
prettyWithConstructor n c l =
  group $ condEnclose (n > 10) "(" ")" $ align $ nest 2 $ vsep (c : l)

printTitle :: String -> IO ()
printTitle s = putStrLn $ "\ESC[34m" <> s <> "\ESC[0m"

printSuccess :: String -> String -> IO ()
printSuccess theory s = putStrLn $ "\ESC[32m[SUCCESS" <> theory <> "]: " <> s <> "\ESC[0m"

printFailure :: String -> String -> IO ()
printFailure theory s = putStrLn $ "\ESC[31m[FAIL" <> theory <> "]: " <> s <> "\ESC[0m"

printWarning :: String -> IO ()
printWarning s = putStrLn $ "\ESC[33m[WARNING]: " <> s <> "\ESC[0m"
