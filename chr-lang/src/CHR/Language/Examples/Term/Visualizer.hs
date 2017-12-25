{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module CHR.Language.Examples.Term.Visualizer
  ( chrVisualize
  )
  where

import           Prelude
import           Data.Maybe
import           Data.List
import qualified Data.Map as Map
import           CHR.Pretty
import qualified CHR.Data.Lookup as Lk
import           CHR.Types
import           CHR.Types.Rule
import           CHR.Language.GTerm.Parser
-- import           UHC.Util.CHR.Solve.TreeTrie.Mono
import           CHR.Solve.MonoBacktrackPrio as MBP
import           CHR.Language.Examples.Term.AST
-- import           UHC.Util.CHR.Solve.TreeTrie.Internal
-- import           UHC.Util.CHR.Solve.TreeTrie.Internal.Shared
import           CHR.Data.Substitutable
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Tree

sortGroupOn :: Ord b => (a -> b) -> [a] -> [[a]]
sortGroupOn f = construct . sortOn f
  where
    construct []     = []
    construct (y:ys) = group : construct rest
      where
        group = y : takeWhile ((f y ==) . f) ys
        rest  =     dropWhile ((f y ==) . f) ys

data NodeData
  -- Applied rule with first alt (if it exists)
  = NodeRule 
    { nrLayer       :: Int
    , nrColumn      :: Int
    , nrName        :: String
    , nrRuleVars    :: [Tm]
    , nrFirstAlt    :: Maybe C
    }
  -- Additional alts of a rule
  | NodeAlt
    { naLayer       :: Int
    , naColumn      :: Int
    , naConstraint  :: C
    }
  -- Added node to make a proper layered graph
  -- A proper layered graph is a graph in which all edges
  -- go from a layer to the next layer. To satisfy this,
  -- we add synthesized nodes on edges that do not skip one
  -- or more layers
  | NodeSynthesized 
    { nsLayer       :: Int
    , nsColumn      :: Int
    , nsEdgeKind    :: EdgeKind
    }

data EdgeKind
  = EdgeGuard -- Usage of term in guard of rule.
  | EdgeHead  -- Usage of term in head of rule.
  | EdgeUnify -- Usage of some term that required unification of this node.
  | EdgeAlt   -- Link between NodeRule and NodeAlt. Both nodes have same layer.
  deriving Eq

type Node' = LNode NodeData
-- | Edge has a kind and a bool that says whether this edge is
--   the last edge of a sequence of edges. The last edge does not
--   end in a synthesized node, the others do.
type Edge' = LEdge (EdgeKind, Bool)
type NodeEdge = (Node', Node', EdgeKind, Bool)

asEdge :: NodeEdge -> Edge'
asEdge ((from, _), (to, _), kind, isLast) = (from, to, (kind, isLast))

-- | Gets the layer of a node
nodeLayer :: Node' -> Int
nodeLayer (_, NodeRule{nrLayer = layer})        = layer
nodeLayer (_, NodeAlt{naLayer = layer})         = layer
nodeLayer (_, NodeSynthesized{nsLayer = layer}) = layer

-- | Gets the column of a node
nodeColumn :: Node' -> Int
nodeColumn (_, NodeRule{nrColumn = col})        = col
nodeColumn (_, NodeAlt{naColumn = col})         = col
nodeColumn (_, NodeSynthesized{nsColumn = col}) = col

-- | Sets the column of a node
nodeSetColumn :: Node' -> Int -> Node'
nodeSetColumn (n, d@NodeRule{}) col        = (n, d{nrColumn = col})
nodeSetColumn (n, d@NodeAlt{}) col         = (n, d{naColumn = col})
nodeSetColumn (n, d@NodeSynthesized{}) col = (n, d{nsColumn = col})

-- | A map between a term, and the location where it was found combined
--   with the required unifications
type NodeMap = Map.Map Tm (Node', [Node'])
-- | Contains all data needed to build the graph, during traversal of
--   the solve trace
data BuildState = BuildState [Node'] [NodeEdge] NodeMap Int Int
emptyBuildState :: BuildState
emptyBuildState = BuildState [] [] Map.empty 0 0

-- | Gives all terms that follow after a unification
replaceInTm :: Tm -> Tm -> Tm -> [Tm]
replaceInTm a b tm
  | tm == a || tm == b = [a, b]
  | otherwise          = case tm of
    Tm_Con name tms -> fmap (Tm_Con name) (replaceList tms)
    Tm_Lst tms ltm  -> do
      tms' <- replaceList tms
      ltm' <- replaceMaybe ltm
      return $ Tm_Lst tms' ltm'
    Tm_Op op tms    -> fmap (Tm_Op op) (replaceList tms)
    x               -> [x]
    where
      replaceList = sequence . fmap (replaceInTm a b)
      replaceMaybe Nothing  = [Nothing]
      replaceMaybe (Just y) = fmap Just $ replaceInTm a b y

-- | Gives all terms in a constraint
tmsInC :: C -> [Tm]
tmsInC (C_Con s tms) = [Tm_Con s tms]
tmsInC _             = []

-- | Gives all terms in a guard
tmsInG :: G -> [Tm]
tmsInG (G_Tm tm) = tmsInTm tm
tmsInG _         = []

tmsInTm :: Tm -> [Tm]
tmsInTm tm = tm : children tm
  where
    children (Tm_Lst as Nothing)  = as
    children (Tm_Lst as (Just a)) = as ++ [a]
    children _                    = [] 

-- | Finds all terms that were used for this rule
--   Used by visualizer to draw edges to the origin of
--   these rules.
precedentTms :: Rule C G P P -> [(Tm, EdgeKind)]
precedentTms rule
  =  fmap (\n -> (n, EdgeHead))  (concatMap tmsInC $ ruleHead rule)
  ++ fmap (\n -> (n, EdgeGuard)) (concatMap tmsInG $ ruleGuard rule)

-- | Adds the constraint (of an alt) to the NodeMap
addConstraint :: C -> Node' -> NodeMap -> NodeMap
addConstraint (CB_Eq a b)   = addUnify a b
addConstraint (C_Con s tms) = addTerm $ Tm_Con s tms
addConstraint c             = const id

addTerm :: Tm -> Node' -> NodeMap -> NodeMap
addTerm tm node =  Map.insert tm (node, [])

addUnify :: Tm -> Tm -> Node' -> NodeMap -> NodeMap
addUnify a b node map = Map.foldlWithKey cb map map
  where
    cb :: NodeMap -> Tm -> (Node', [Node']) -> NodeMap
    cb map' tm (n, nodes) = foldl (\map'' key -> Map.insertWith compare key (n, node : nodes) map'') map' (replaceInTm a b tm)
    compare x@(_, nodes1) y@(_, nodes2)
      | length nodes1 <= length nodes2 = x
      | otherwise                      = y

-- | Generates nodes and edges for a SolveStep.
--   Stores the resulting terms in the NodeMap.
stepToNodes :: BuildState -> SolveStep' C (MBP.StoredCHR C G P P) S -> BuildState
stepToNodes state@(BuildState _ _ nodeMap nodeId layer) step
  = BuildState
    nodes
    edges''
    nodeMap'
    nodeId'
    layer'
  where
    schr = stepChr step
    rule = storedChrRule' schr
    updRule = varUpd (stepSubst step) rule
    alt = maybe [] (fmap $ varUpd $ stepSubst step) $ stepAlt step
    (BuildState nodes edges' nodeMap' nodeId' layer', primaryNode) =
      createNodes
        (maybe "[untitled]" id (ruleName rule))
        (Lk.elems (stepSubst step))
        alt
        state
    edges'' =
      ( fmap (\(n, kind) -> (n, primaryNode, kind, True))
        $ concatMap (\(n, ns, kind) -> (n, kind) : fmap (\x -> (x, EdgeUnify)) ns)
        $ mapMaybe
          (\(tm, kind) -> fmap
            (\(n, ns) -> (n, ns, kind))
            (Map.lookup tm nodeMap))
          (precedentTms updRule)
      )
      ++ edges'

createNodes :: String -> [Tm] -> [C] -> BuildState -> (BuildState, Node')
createNodes name vars alts (BuildState previousNodes previousEdges nodeMap nodeId layer)
  = ( BuildState (nodes ++ previousNodes) (edges ++ previousEdges) nodeMap' (nodeId + max 1 (length alts)) (layer + 1)
    , primaryNode
    )
  where
    primaryNode =
      (nodeId, NodeRule
        { nrLayer    = layer
        , nrColumn   = 0
        , nrName     = name
        , nrRuleVars = vars
        , nrFirstAlt = listToMaybe alts
        }
      )
    nodes = primaryNode : altNodes
    altTms = concatMap tmsInC alts
    nodeMap' = foldl updateMap nodeMap nodes
    -- Updates node map for a new node
    updateMap :: NodeMap -> Node' -> NodeMap
    updateMap map node@(_, NodeRule{ nrFirstAlt = Just alt }) = addConstraint alt node map
    updateMap map node@(_, NodeAlt{ naConstraint = alt }) = addConstraint alt node map
    updateMap map _ = map
    
    altNode (constraint, i) = (nodeId + i, NodeAlt layer 0 constraint)
    altNodes = fmap altNode (drop 1 $ addIndices alts)
    edges = (fmap (\n -> (primaryNode, n, EdgeAlt, True)) altNodes)

-- | Adds synthesized nodes to create a proper layered graph
createSynthesizedNodes :: [Node'] -> [NodeEdge] -> Int -> ([NodeEdge], [Node'])
createSynthesizedNodes nodes es firstNode
  = create es firstNode [] []
  where
    create :: [NodeEdge] -> Int -> [NodeEdge] -> [Node'] -> ([NodeEdge], [Node'])
    create ((edge@(from, to, kind, _)):edges) id accumEdges accumNodes
      = create edges id' (es ++ accumEdges) (ns ++ accumNodes)
      where
        (es, ns, id') = split (nodeLayer from) edge id
    create _ _ accumEdges accumNodes = (accumEdges, accumNodes)
    split :: Int -> NodeEdge -> Int -> ([NodeEdge], [Node'], Int)
    split fromLayer edge@(from, to, kind, _) id
      | fromLayer + 1 >= nodeLayer to = ([edge], [], id)
      | otherwise                     =
        ( (from, node, kind, False) : edges',
          node : nodes',
          id'
        )
        where
          node = (id, (NodeSynthesized (fromLayer + 1) 0 kind))
          (edges', nodes', id') = split (fromLayer + 1) (node, to, kind, True) (id + 1)

-- | Creates a graph with the visualization
createGraph :: [C] -> [SolveStep' C (MBP.StoredCHR C G P P) S] -> Gr NodeData (EdgeKind, Bool)
createGraph query steps = mkGraph sortedLayers (fmap asEdge edges)
  where
    -- | Sort the layers by giving each node in a layer an unique nodeColumn value
    sortedLayers = sortedFirstLayer ++ sortNodes maxLayerSize (sortedFirstLayer : layers) layeredEdges
    -- | Set the nodeColumn values of each of the nodes in the query (the query forms the first layer)
    sortedFirstLayer = uniqueColumns firstLayer ((maxLayerSize - length firstLayer) `div` 2)
    -- | Extracting [[Node']] from layerNodes
    firstLayer : layers = sortGroupOn nodeLayer nodes
    -- firstLayer : layers = Map.elems $ layerNodes nodes
    -- | For each layer we create a list with the nodes in that layer
    -- layerNodes :: [Node'] -> Map.Map Int [Node']
    -- layerNodes ns = foldl (\m x -> Map.insertWith (++) (nodeLayer x) [x] m) Map.empty ns
    (state, _) = createNodes "?" [] query emptyBuildState
    BuildState nodes' edges' _ id _ = foldr (flip stepToNodes) state steps
    (edges, synNodes) = createSynthesizedNodes nodes' edges' id
    nodes = nodes' ++ synNodes
    maxLayerSize = maximum $ fmap length (firstLayer : layers)
    edgesCrossLayer = filter (\(from, to, _, _) -> nodeLayer from /= nodeLayer to) edges
    layeredEdges = sortGroupOn (nodeLayer . fst') edgesCrossLayer

-- | Sort the nodes using the median heuristic
-- | The first layer is left as it was, the second layer is sorted using the first etc.
sortNodes :: Int -> [[Node']] -> [[NodeEdge]] -> [Node']
sortNodes _ (x:[]) _ = []
sortNodes maxLayerSize (x:xs:xss) e = medianHeurstic maxLayerSize x xs edges ++ sortNodes maxLayerSize (xs:xss) rest
  where
    (edges, rest) =
      if null e then
        ([], [])
      else if (nodeLayer $ fst' $ head $ head e) == nodeLayer (head x) then
        (head e, tail e)
      else
        ([], e)

-- | lowerLayer is the layer to be sorted, upperLayer is assumed to be sorted
-- | The maxLayerSize is used to center the graph (by altering the value given to uniqueColumns)
-- | Documentation for the median heuristic:
-- | https://cs.brown.edu/~rt/gdhandbook/chapters/hierarchical.pdf
-- | http://www.cs.usyd.edu.au/~shhong/fab.pdf
-- | https://books.google.nl/books?id=6hfsCAAAQBAJ&lpg=PA28&dq=median%20heuristic%20sorting%20vertices&hl=nl&pg=PA28#v=onepage&q&f=false
medianHeurstic :: Int -> [Node'] -> [Node'] -> [NodeEdge] -> [Node']
medianHeurstic maxLayerSize upperLayer lowerLayer e = uniqueColumns sortedMedianList ((maxLayerSize - length lowerLayer) `div` 2)
  where
    -- | The medianList sorted on the median values
    sortedMedianList = sortOn nodeColumn medianList
    -- | The list of median values for each of the nodes in lowerLayer
    medianList = map (\x -> nodeSetColumn x (median x)) lowerLayer
    -- | The median value of the x coördinates of the neighbors
    median n
      | neighborCount == 0 = 0
      | otherwise          = coords !! (ceiling (realToFrac neighborCount / 2) - 1)
      where
        coords = coordinates n
        neighborCount = length coords
    -- | The values of the x coördinates of the neighbors
    coordinates n = map nodeColumn (neighbors n)
    -- | The neighbor nodes of the given Node' n (on a higher layer)
    neighbors n = map (fst') (edges n)
    -- | All the edges connected to given Node' n
    edges n = filter (\(_, (id, _), _, _) -> id == fst n) e

-- | Ensure that each Node' has an unique nodeColumn (the x coördinate)
-- | The value of the nodeColumn is set to i
uniqueColumns :: [Node'] -> Int -> [Node']
uniqueColumns (n:ns) i = nodeSetColumn n i : uniqueColumns ns (i + 1)
uniqueColumns _ _ = []

fst' :: (a, b, c, d) -> a
fst' (a, _, _, _) = a

-- | Creates a HTML tag
tag :: String -> PP_Doc -> PP_Doc -> PP_Doc
tag name attr content = (text ("<" ++ name)) >|< attributes attr >|< body content
  where
    attributes Emp = Emp
    attributes a   = text " " >|< a
    body Emp       = text " />"
    body content   = text ">" >|< content >|< text ("</" ++ name ++ ">")

-- | Creates a HTML tag without attributes
tag' :: String -> PP_Doc -> PP_Doc
tag' name = tag name Emp

-- | Add indices to an array as a tuple with value and index
addIndices :: [a] -> [(a, Int)]
addIndices = flip zip [0..]

-- | Generates HTML for a node
showNode :: (Node' -> (Int, Int)) -> Node' -> PP_Doc
showNode pos node@(_, NodeRule{nrLayer = layer, nrName = name, nrRuleVars = vars, nrFirstAlt = alt}) = tag "div"
  (
    text "class=\"rule\" style=\"top: "
    >|< pp (y + 10) 
    >|< text "px; left: "
    >|< pp x
    >|< text "px;\""
  )
  (
    tag "span" (text "class=\"" >|< className >|< text "\"") (
      (text name)
      >|< (hlist (fmap ((" " >|<) . pp) vars))
    )
    >|< tag' "br" Emp
    >|< text "&#8627;"
    >|< tag "span" (text "class=\"rule-alt\"") altText
  )
  where
    (x, y) = pos node
    altText = maybe (text ".") pp alt
    className = text "rule-text"
    showUsage name var = tag "div" (text $ "class=\"" ++ className ++ "\"") (text " ")
      where
        className = name ++ " var-" ++ var
showNode pos node@(_, NodeAlt{ naConstraint = constraint }) = tag "div"
  (
    text "class=\"rule-additional-alt\" style=\"top: "
    >|< pp (y + 10)
    >|< text "px; left: "
    >|< pp x
    >|< text "px;\""
  )
  (
    text "&#8627;"
    >|< tag "span" (text "class=\"rule-alt\"") (pp constraint)
  )
  where
    (x, y) = pos node
showNode _ (_, NodeSynthesized{}) = Emp

-- | Generates HTML for an edge
showEdge :: (Node -> (Int, Int)) -> Edge' -> PP_Doc
showEdge pos (from, to, (kind, isEnd)) =
  if kind == EdgeAlt then
    -- Edge between rule and alt of same rule
    tag "div"
      (
        text "class=\"edge-alt\" style=\"top: "
        >|< pp y1
        >|< "px; left: "
        >|< pp (min x1 x2)
        >|< "px; width: "
        >|< abs (x2 - x1 - 16)
        >|< "px;\""
      )
      (text " ")
  else
    tag "div"
      (
        text "class=\"edge-ver "
        >|< text className
        >|< text "\" style=\"top: "
        >|< pp (y1 + 35)
        >|< "px; left: "
        >|< pp x1
        >|< "px; height: "
        >|< (y2 - y1 - 60 - 6)
        >|< "px;\""
      )
      (text " ")
    >|< tag "div"
      (
        text "class=\"edge-hor"
        >|< text (if x2 > x1 then " edge-hor-left " else if x2 < x1 then " edge-hor-right " else " edge-hor-no-curve ")
        >|< text className
        >|< text "\" style=\"top: "
        >|< pp (y2 - 19)
        >|< "px; left: "
        >|< pp (if x1 < x2 then x1 else x2 + (if isEnd then 0 else (abs (x2 - x1) + 1) `div` 2))
        >|< "px; width: "
        >|< pp (abs (x2 - x1) `div` (if isEnd then 1 else 2))
        >|< "px;\""
      )
      (text " ")
    >|< (if isEnd then Emp else tag "div"
        (
          text "class=\"edge-end edge-end-"
          >|< text (if x2 > x1 then "left " else if x2 < x1 then "right " else "no-curve ")
          >|< text className
          >|< text "\" style=\"top: "
          >|< pp (y2 - 3 + 11)
          >|< "px; left: "
          >|< pp (if x1 < x2 then (x1 + x2) `div` 2 + 6 else x2)
          >|< pp "px; width: "
          >|< pp (if x1 == x2 then 0 else ((abs (x2 - x1) + 1) `div` 2) - 6)
          >|< "px;\""
        )
        (text " ")
    )
  where
    (x1, y1)  = pos from
    (x2, y2)  = pos to
    className = case kind of
      EdgeAlt   -> ""
      EdgeGuard -> "edge-guard"
      EdgeHead  -> "edge-head"
      EdgeUnify -> "edge-unify"

-- | Creates a visualization for the given query and solve trace.
--   Output is a PP_Doc containing a HTML file.
chrVisualize :: [C] -> SolveTrace' C (MBP.StoredCHR C G P P) S -> PP_Doc
chrVisualize query trace = tag' "html" $
  tag' "head" (
    tag' "title" (text "CHR visualization")
    >|< tag' "style" styles
  )
  >|< tag' "body" (
    body
  )
  where
    graph = createGraph query trace
    body = ufold reduce Emp graph >|< hlist (fmap (showEdge posId) $ labEdges graph)
    reduce (inn, id, node, out) right = showNode pos (id, node) >|< right
    nodeCount = length $ nodes graph
    pos :: Node' -> (Int, Int)
    pos n = ((nodeColumn n) * 200, (nodeLayer n) * 60)
    posId :: Node -> (Int, Int)
    posId node = pos (node, fromJust $ lab graph node)

-- | The stylesheet used in the visualization.
styles :: PP_Doc
styles =
  text "body {\n\
       \  font-size: 9pt;\n\
       \  font-family: Arial;\n\
       \}\n\
       \.rule {\n\
       \  position: absolute;\n\
       \  white-space: nowrap;\n\
       \}\n\
       \.rule-text {\n\
       \  border: 1px solid #aaa;\n\
       \  background-color: #fff;\n\
       \  display: inline-block;\n\
       \  padding: 2px;\n\
       \  margin: 3px 1px 0;\n\
       \  min-width: 30px;\n\
       \  text-align: center;\n\
       \}\n\
       \.rule-alt {\n\
       \  display: inline-block;\n\
       \  color: #A89942;\n\
       \  background: #fff;\n\
       \}\n\
       \.rule-additional-alt {\n\
       \  position: absolute;\n\
       \  white-space: nowrap;\n\
       \  margin-top: 24px;\n\
       \}\n\
       \.edge-ver {\n\
       \  position: absolute;\n\
       \  width: 0px;\n\
       \  border-left: 6px solid #578999;\n\
       \  opacity: 0.4;\n\
       \  margin-left: 15px;\n\
       \  margin-top: 9px;\n\
       \  z-index: -1;\n\
       \}\n\
       \.edge-hor {\n\
       \  position: absolute;\n\
       \  height: 27px;\n\
       \  border-bottom: 6px solid #578999;\n\
       \  opacity: 0.4;\n\
       \  margin-left: 15px;\n\
       \  margin-top: 8px;\n\
       \  z-index: -1;\n\
       \}\n\
       \.edge-diag {\n\
       \  transform-origin: 50% 50%;\n\
       \  position: absolute;\n\
       \  height: 6px;\n\
       \}\n\
       \.edge-hor-left {\n\
       \  border-bottom-left-radius: 100% 33px;\n\
       \  border-left: 6px solid #578999;\n\
       \}\n\
       \.edge-hor-right {\n\
       \  border-bottom-right-radius: 100% 33px;\n\
       \  border-right: 6px solid #578999;\n\
       \}\n\
       \.edge-hor-no-curve {\n\
       \  border-right: 6px solid #578999;\n\
       \}\n\
       \.edge-end {\n\
       \  position: absolute;\n\
       \  height: 27px;\n\
       \  width: 16px;\n\
       \  border-top: 6px solid #578999;\n\
       \  opacity: 0.4;\n\
       \  margin-left: 15px;\n\
       \  margin-top: 8px;\n\
       \  z-index: -1;\n\
       \}\n\
       \.edge-end-left {\n\
       \  border-top-right-radius: 100% 33px;\n\
       \  border-right: 6px solid #578999;\n\
       \}\n\
       \.edge-end-no-curve {\n\
       \  border-right: 6px solid #578999;\n\
       \  margin-top: 14px;\n\
       \  height: 21px;\n\
       \}\n\
       \.edge-end-right {\n\
       \  border-top-left-radius: 100% 33px;\n\
       \  border-left: 6px solid #578999;\n\
       \}\n\
       \.edge-guard {\n\
       \  border-color: #69B5A7;\n\
       \}\n\
       \.edge-unify {\n\
       \  border-color: #8CBF7A;\n\
       \}\n\
       \.edge-alt {\n\
       \  height: 1px;\n\
       \  background-color: #aaa;\n\
       \  position: absolute;\n\
       \  margin-top: 19px;\n\
       \  z-index: -1;\n\
       \  padding-right: 22px;\n\
       \}\n\
       \"
