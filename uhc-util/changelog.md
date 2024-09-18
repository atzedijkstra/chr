# Changelog

## 0.1.7.0

- [incompatibility] with previous versions, CHR (and required code) moved to separate libs chr-*
- [compatibility] with ghc 8.2.x

## 0.1.6.8

- [api] addition of replacement for TreeTrie required for CHR solving (gives x4 performance improvement), also forcing changes in uhc
- [api] rewrite of scoped lookup/map

## 0.1.6.7

## 0.1.6.6

- [compatibility] with ghc 8.0.1
- [chr engine] development, examples, debugging, ...
- [libs] removed dependency on syb (and Data instances)

## 0.1.6.5

- [libs] updated version lowerbound for hashable and fclabels
- [chr] dependency on logict-state lib, as prep for new solver
- [chr] CHR rules have an additional priority field, as prep for new solver
- [api] additional PP instances
- [serialize] generic impl of Serialize more efficiently generates tags (1 per datatype instead of log(nr of constructors))

## 0.1.6.4

- [api] move of RLList functionality encoding lexical scoping to separate module LexScope (taken from UHC)

## 0.1.6.3

- [api] move of RLList, TreeTrie, CHR, Substitutable (partial) from uhc to uhc-util

## 0.1.6.2

- [uhc] as released with uhc 1.1.9.1

## 0.1.5.5

- [compatibility] GHC 7.10 compatibility: sortOn has become more strict, addition of a sortOnLazy

## 0.1.5.4 - 20150416

- [build] changelog.md included in cabal dist

## 0.1.5.3 - 20150402

- [build] depends on uulib>=0.9.19 to avoid Applicative hiding imports

## 0.1.5.2 - 20150401

- [build] should work with ghc 7.10


