-- ~~ TODO:

-- ~ Write explicit return types for functions


-- ~~ NOTES:

-- ~ Parent vector -1 root pointer:
--   To simplify code we have let the root pointer be -1 as opposed to self-referencing
--   pointer.

-- ~ Naive parent-vtree conversion version:
--   Assumes Euler tour of tree (like some other general operations). Need for slow computatipn of subtree sizes.
--   Simple and efficient if tree given in Euler tour and subtree sizes already known.

-- ~ Validates:
--   Implementation validate on all three parent trees of AS3 and the example tree of
--   from Blelloch P. 85.


-- ~~ FURTHER IDEAS:

-- ~ Benchamrk compare Rasmus' and Martins' conversions on different backends and compared to each other.
-- ~ Benchmark differences between directed vs. undirected vgraph conversions <hard to random generate large trees>.

-- ~ Perform convertions BACK from vtree to parents or to vgraphs
-- ~ Perform advanced (unconstrained) conversion from undirected vgraph to parents.
-- ~ Implement the splitting and merging vtree operations.



import "helpers"
import "martin"

type constraint = #inner | #outer | #full




--------------------------------------------------
----------- CONCEPTUAL IMPLEMENTATION ------------
--------------------------------------------------

-- | Converts from plain tree (with parent
-- vector in Euler Tour form and root with
-- parent 0) to vtree.
--
-- ~~ Complexity <n: nodes, d: depth>
-- ~ general:
-- Work: O(n lg n  +  W(find_subtree_sizes)),
-- Span: O(lg n  +    S(find_subtree_sizes))
-- ~ with 'subtree_sizes_advanced':
-- Work: O(n lg n), Span: O(n lg n) (worst case)
-- Work: O(n lg n), Span: O(lg n) (practice)
def parents_to_vtree_naive [n] (parents: [n]i64) =

	let sizes_ = replicate n 1i64
	let depths_ = map (\p -> if p == -1 then 0 else 1) parents

	let (sizes, depths, _) = -- (Wyllie ranking)
		loop (sizes_, depths_, parents)
		while any (\x -> x != -1) parents do

			-- accumulates depth updates
			let depths = 
				map (\i -> 
					if parents[i] == -1 then depths_[i] 
					else depths_[i] + depths_[parents[i]]) 
				(iota n)

			-- accumulates size updates
			let sizes = reduce_by_index sizes_ (+) 0 parents (copy sizes_)

			-- updates parents
			let parents' =
				map (\p -> 
					if p == -1 then -1
					else parents[p]
				) parents

			in  (sizes, depths, parents')	


	-- finds left-paren offsets through
	-- depths differences.
	let depths_prev = rotate (-1) depths
	let left_offsets = 
		map2 (\d_curr d_prev ->
			if d_curr == 0 then 0
			else d_prev - d_curr + 2
		) depths depths_prev
	
	let left_paren = scan (+) 0 left_offsets 

	-- computes left-parens through right-
	-- parens and subtree sizes.
	let right_paren = 
		map2 (\left size ->
			left + size * 2 - 1
		) left_paren sizes
	
	in (left_paren, right_paren)



-- | Filters and normalizes the pointers
-- of an undirected 'vgraph' given an array
-- of boolean predicates 'po_parents'.
-- Work: O(n lg n), Span: O(lg n).
def filter_parents [m] [n] (root: i64)
				   (vgraph: ([m]i64, [n]i64, [m]f32))
				   (po_parents: *[n]bool) =
		
	-- unpacks vgraph
	let (segments, pointers, values) = vgraph

	-- computes segment metadata (flags, indicies of segment start)
	let (segs_start, segs_dist) = mkFlagArray (map u32.i64 segments) 0 (iota m) :> ([m]u32, [n]i64)
	let flags = map bool.i64 segs_dist with [0] = true
	let segs_start = map i64.u32 segs_start -- B1

	-- computes pointer lookup arrays 
	-- (current segment (II1), local index (II2), and size offsets).
	let po_seg = sgmScan (+) 0 flags segs_dist -- II1 
	let po_parents' = po_parents with [segs_start[root]] = true
	let po_order = map2 (\i sgm -> i - segs_start[sgm]) (iota n) po_seg -- II2
	let seg_offs = [1] ++ (init segments) |> scan (\s1 s2 -> s1 + s2 - 1) 0

	-- adjusts pointers to reference the start of their segments
	-- and filters subsequent parent pointers given 'po_parents'.
	let pointers_norm = map (\p -> p - po_order[p]) pointers
	let (parents_, _) = 
		zip pointers_norm po_parents'
		|> filter (\(_, ps) -> ps) 
		|> unzip :> ([m]i64, [m]bool)

	-- adjusts parent pointers to filtered indicies
	-- by subtracting cumulative size offsets.
	let parents = 
		map (\i -> 
			let seg = po_seg[parents_[i]]
			in parents_[i] - seg_offs[seg]
		) (iota m) with [root] = -1
	
	in (parents, values)



-- | Converts from an undirected 'vgraph' tree to a parent vector
-- tree given the 'root' index.
-- Assumes an internally ordered vgraph, where the parent pointer
-- is the first in its segment.
-- Work: O(n lg n), Span: O(lg n).
def undirected_vgraph_to_parents_inner [m] [n] (root: i64) 
									   (vgraph: ([m]i64, [n]i64, [m]f32)) =

	-- constructs parent pointers predicates 
	-- (given by initial flags) before filtering. 
	let (segments, _ , _) = vgraph 
	let (_, flags) = mkFlagArray (map u32.i64 segments) false (replicate m true) :> ([]u32, [n]bool)
	in filter_parents root vgraph flags



-- | Converts from an undirected 'vgraph' tree to a parent vector
-- tree given the 'root' index.
-- Assumes an externally ordered vgraph, where all parent nodes
-- precede their children in the array layout.
-- Work: O(n lg n), Span: O(lg n).
def undirected_vgraph_to_parents_outer [m] [n] (vgraph: ([m]i64, [n]i64, [m]f32)) =

	let (segments, pointers , _) = vgraph 

	-- computes start of current segment for each pointer
	let (segs_start, segs_dist) = mkFlagArray (map u32.i64 segments) 0 (iota m) :> ([m]u32, [n]i64)
	let flags = map bool.i64 segs_dist with [0] = true
	let segs_start = map i64.u32 segs_start -- B1
	let po_segstart = scatter (replicate n 0) segs_start segs_start |> sgmScan (+) 0 flags

	-- constructs pointer predicates by
	-- locating backwards pointers.
	let po_parents =
		zip pointers (iota n)
		|> map (\(p, i) -> p < po_segstart[i] || i == 0)

	in filter_parents 0 vgraph po_parents


-- | Converts from an undirected 'vgraph' tree to a parent vector
-- tree given the 'root' index.
-- Makes no assumptions (but sacrifices speed).
-- Work: O(n lg n + d * n), Span: O(lg n + d) <d: tree depth>.
def undirected_vgraph_to_parents_full [m] [n] (root: i64)
									  (vgraph: ([m]i64, [n]i64, [m]f32)) =
	
	let (segments, pointers, _) = vgraph

	-- computes segment metadata (flags)
	let (_, segs_dist) = mkFlagArray (map u32.i64 segments) 0 (iota m) :> ([m]u32, [n]i64)
	let flags = map bool.i64 segs_dist with [0] = true

	-- computes pointer lookup arrays 
	-- (current, segment, active segment, next 
	-- segments to activate, visited parents).
	let po_seg = sgmScan (+) 0 flags segs_dist -- II1 
	let po_active = map (\p -> p == root) po_seg
	let po_next = map2 (\p a -> if a then p else -1) pointers po_active
	let po_parents = replicate n false

	-- traverses the tree to locate
	-- parent pointers.
	let (po_parents', _) =
		loop (po_parents, po_next)
		while any (\p -> p != -1) po_next do

			-- marks found parents and child segments to be activated
			let po_parents' = scatter po_parents po_next (replicate n true)
			let seg_ids = map (\p -> if p == -1 then -1 else po_seg[p]) po_next
			let segs_active = scatter (replicate m false) seg_ids (replicate n true)

			-- finds parent pointers
			-- for subsequent iteration.
			let po_next' = 
				map2 (\i ps -> 
					if segs_active[po_seg[i]] && not ps
					then pointers[i] 
					else -1
				) (iota n) po_parents'

			in (po_parents', po_next')
	
	in filter_parents root vgraph po_parents'




--------------------------------------------------
------------- INLINED IMPLEMENTATION -------------
--------------------------------------------------

def undirected_vgraph_to_parents_inner' [m] [n] (root: i64) 
									   (vgraph: ([m]i64, [n]i64, [m]f32)) =

	let (segments, pointers, values) = vgraph 

	let (segs_start, segs_dist) = mkFlagArray (map u32.i64 segments) 0 (iota m) :> ([m]u32, [n]i64)
	let flags = map bool.i64 segs_dist with [0] = true
	let segs_start = map i64.u32 segs_start

	let po_seg = sgmScan (+) 0 flags segs_dist
	let po_order = map2 (\i sgm -> i - segs_start[sgm]) (iota n) po_seg
	let segment_offsets = [1] ++ (init segments) |> scan (\s1 s2 -> s1 + s2 - 1) 0

	let pointers_norm = map (\p -> p - po_order[p]) pointers
	let (pointer_ps, _) =
		zip pointers_norm flags
		|> filter (\(_, f) -> f)
		|> unzip

	let parents =
		map (\i -> 
			let segment = po_seg[pointer_ps[i]]
			in if segment == i then -1
		   else pointer_ps[i] - segment_offsets[segment]
		) (indices pointer_ps) with [root] = -1
	
	in (parents, values)



def undirected_vgraph_to_parents_outer' [m] [n] (vgraph: ([m]i64, [n]i64, [m]f32)) =

	let (segments, pointers, values) = vgraph 

	let (segs_start, segs_dist) = mkFlagArray (map u32.i64 segments) 0 (iota m) :> ([m]u32, [n]i64)
	let flags = map bool.i64 segs_dist with [0] = true
	let segs_start = map i64.u32 segs_start

	let po_seg = sgmScan (+) 0 flags segs_dist
	let po_segstart = scatter (replicate n 0) segs_start segs_start |> sgmScan (+) 0 flags
	let po_order = map2 (\i sgm -> i - segs_start[sgm]) (iota n) po_seg
	let segment_offsets = [1] ++ (init segments) |> scan (\s1 s2 -> s1 + s2 - 1) 0

	let pointers_norm = map (\p -> p - po_order[p]) pointers
	let (pointer_ps, _) =
		zip pointers_norm (iota n)
		|> filter (\(p, i) -> p < po_segstart[i] || i == 0)
		|> unzip

	let parents =
		map (\i -> 
			let segment = po_seg[pointer_ps[i]]
			in if segment == i then -1
		       else pointer_ps[i] - segment_offsets[segment]
		) (indices pointer_ps) 
		with [0] = -1
	
	in (parents, values)



def undirected_vgraph_to_parents_full' [m] [n] (root: i64)
									  (vgraph: ([m]i64, [n]i64, [m]f32)) =
	
	let (segments, pointers, values) = vgraph

	let (segs_start, segs_dist) = mkFlagArray (map u32.i64 segments) 0 (iota m) :> ([m]u32, [n]i64)
	let flags = map bool.i64 segs_dist with [0] = true
	let segs_start = map i64.u32 segs_start

	let po_seg = sgmScan (+) 0 flags segs_dist
	let po_active = map (\p -> p == root) po_seg
	let po_next = map2 (\p a -> if a then p else -1) pointers po_active
	let po_parents = replicate n false

	let (po_parents', _) =
		loop (po_parents, po_next)
		while any (\p -> p != -1) po_next do

			let po_parents' = scatter po_parents po_next (replicate n true)
			let seg_ids = map (\p -> if p == -1 then -1 else po_seg[p]) po_next
			let segs_active = scatter (replicate m false) seg_ids (replicate n true)
			let po_next' = map2 (\i ps -> if segs_active[po_seg[i]] && not ps then pointers[i] else -1) (iota n) po_parents'

			in (po_parents', po_next')
		
	let po_parents'' = po_parents' with [segs_start[root]] = true
	let po_order = map2 (\i sgm -> i - segs_start[sgm]) (iota n) po_seg
	let seg_offs = [1] ++ (init segments) |> scan (\s1 s2 -> s1 + s2 - 1) 0

	let pointers_norm = map (\p -> p - po_order[p]) pointers
	let (parents_, _) = zip pointers_norm po_parents'' |> filter (\(_, ps) -> ps) |> unzip :> ([m]i64, [m]bool)

	let parents = 
		map (\i -> 
			let seg = po_seg[parents_[i]]
			in parents_[i] - seg_offs[seg]
		) (iota m) with [root] = -1
	
	in (parents, values)



def undirected_vgraph_to_vtree [m] [n] 't (constr: constraint)
							   (parents_conv: [m]i64 -> ([]t, []t))
							   (root: i64)
							   (vgraph: ([m]i64, [n]i64, [m]f32)) =

	let (parents, _) =
		match constr
			case #inner -> undirected_vgraph_to_parents_inner root vgraph
			case #outer -> undirected_vgraph_to_parents_outer vgraph
			case #full  -> undirected_vgraph_to_parents_full root vgraph
	
	in parents_conv (parents :> [m]i64)

--- Example execution: 
--	undirected_vgraph_to_vtree 
--		#outer parents_to_vtree_naive 0i64
--     	([2i64,4i64,1i64,1i64,1i64,1i64],
--      [2i64,9i64, 0i64,6i64,7i64,8i64, 3i64, 4i64, 5i64, 1i64],
--      (replicate 6 0))




--------------------------------------------------
-------------------- TESTING ---------------------
--------------------------------------------------

-- | Makes a full binary parent tree
-- in Euler tour format.
def make_binary_parents (len: i64) =
	let tree = 
		map (\i -> 
			if i % 2 == 1 then (i-1) / 2
			else i / 2
		) (iota len)
	
	in tree with [0] = -1



entry validate__parents_to_vgraph [n] (parents: [n]i64) =
	let (left1, right1) = (parents_to_vtree parents)
	let res1 = (map i64.i32 (left1 :> [n]i32),
				map i64.i32 (right1 :> [n]i32))

	let res2 = parents_to_vtree_naive parents
	in res1 == res2

-- ~~ DESCRIPTION:
-- ~ Test of AS3 tree 1, 2, and 3.
-- ~ Test of V-tree from Blelloch P. 85
-- == 
-- entry: validate__parents_to_vgraph
-- compiled nobench input { [-1i64, 0i64, 1i64, 0i64] } 
-- output { true }
-- compiled nobench input { [-1i64, 0i64, 0i64, 0i64, 3i64, 3i64, 0i64, 6i64] }
-- output { true }
-- compiled nobench input { [-1i64, 0i64, 1i64, 2i64, 3i64] }
-- output { true }
-- compiled nobench input { [-1i64, 0i64, 1i64, 1i64, 1i64, 0i64] }
-- output { true }



entry test__parents_to_vtree_naive [n] (parents: [n]i64) =
	parents_to_vtree_naive parents

-- ~~ DESCRIPTION:
-- ~ Test of AS3 tree 1, 2, and 3.
-- ~ Test of V-tree from Blelloch P. 85
-- == 
-- entry: test__parents_to_vtree_naive
-- compiled nobench input { [-1i64, 0i64, 1i64, 0i64] }
-- output { [0i64, 1i64, 2i64, 5i64 ] [7i64, 4i64, 3i64, 6i64] }
-- compiled nobench input { [-1i64, 0i64, 0i64, 0i64, 3i64, 3i64, 0i64, 6i64] }
-- output { [0i64, 1i64, 3i64, 5i64, 6i64, 8i64, 11i64, 12i64]
--			[15i64, 2i64, 4i64, 10i64, 7i64, 9i64, 14i64, 13i64] }
-- compiled nobench input { [-1i64, 0i64, 1i64, 2i64, 3i64] }
-- output { [0i64, 1i64, 2i64, 3i64, 4i64] [9i64, 8i64, 7i64, 6i64, 5i64] }
-- compiled nobench input { [-1i64, 0i64, 1i64, 1i64, 1i64, 0i64] }
-- output { [0i64, 1i64, 2i64, 4i64, 6i64, 9i64]
--			[11i64, 8i64, 3i64, 5i64, 7i64, 10i64] }



entry test__undirected_vgraph_to_parents_inner [m] [n] (root: i64) 
											   (segments: [m]i64) 
											   (pointers: [n]i64) =

	let values = replicate m 0
	let vgraph = (segments, pointers, values)
	let (parents, _) =
		undirected_vgraph_to_parents_inner' root vgraph

	in parents

-- ~~ DESCRIPTION:
-- ~ Test of AS3 tree 1, 2, and 3 ('inner' constrained).
-- ~ Test of V-tree from Blelloch P. 85
-- ==
-- entry: test__undirected_vgraph_to_parents_inner
-- compiled nobench input { 3i64 [1i64,1i64,2i64,2i64] [4i64, 3i64, 5i64,1i64, 0i64,2i64] }
-- output { [3i64,2i64,3i64,-1i64] }
-- compiled nobench input { 7i64 [1i64,1i64,3i64,1i64,1i64,2i64,1i64,4i64] [10i64, 11i64, 12i64,5i64,6i64, 3i64, 4i64, 13i64,9i64, 8i64, 0i64,1i64,2i64,7i64] }
-- output { [7i64,7i64,7i64,2i64,2i64,7i64,5i64,-1i64] }
-- compiled nobench input { 2i64 [2i64,2i64,1i64,2i64,1i64] [4i64,2i64, 1i64,5i64, 0i64, 3i64,7i64, 6i64] }
-- output { [2i64,0i64,-1i64,1i64,3i64] }
-- compiled nobench input { 5i64 [1i64,4i64,1i64,1i64,1i64,2i64] [8i64, 9i64,5i64,6i64,7i64, 2i64, 3i64, 4i64, 0i64,1i64] }
-- output { [5i64,5i64,1i64,1i64,1i64,-1i64] }



entry test__undirected_vgraph_to_parents_outer [m] [n]
											   (segments: [m]i64) 
											   (pointers: [n]i64) =

	let values = replicate m 0
	let vgraph = (segments, pointers, values)
	let (parents, _) =
		undirected_vgraph_to_parents_outer' vgraph

	in parents

-- ~~ DESCRIPTION:
-- ~ Test of AS3 tree 1, 2, and 3 ('outer' constrained).
-- ~ Test of V-tree from Blelloch P. 85
-- ==
-- entry: test__undirected_vgraph_to_parents_outer
-- compiled nobench input { [2i64,2i64,1i64,1i64] [2i64,5i64, 0i64,4i64, 3i64, 1i64] }
-- output { [-1i64,0i64,1i64,0i64] }
-- compiled nobench input { [4i64,1i64,1i64,3i64,1i64,1i64,2i64,1i64] [5i64,4i64,11i64,8i64, 1i64, 0i64, 9i64,10i64,3i64, 6i64, 7i64, 2i64,13i64,12i64] }
-- output { [-1i64,0i64,0i64,0i64,3i64,3i64,0i64,6i64] }
-- compiled nobench input { [1i64,2i64,2i64,2i64,1i64] [1i64, 0i64,4i64, 5i64,2i64, 3i64,7i64, 6i64] }
-- output { [-1i64,0i64,1i64,2i64,3i64] }
-- compiled nobench input { [2i64,4i64,1i64,1i64,1i64,1i64] [2i64,9i64, 0i64,6i64,7i64,8i64, 3i64, 4i64, 5i64, 1i64] }
-- output { [-1i64,0i64,1i64,1i64,1i64,0i64] }



entry test__undirected_vgraph_to_parents_full [m] [n] (root: i64) 
											  (segments: [m]i64) 
											  (pointers: [n]i64) =

	let values = replicate m 0
	let vgraph = (segments, pointers, values)
	let (parents, _) =
		undirected_vgraph_to_parents_full' root vgraph

	in parents

-- ~~ DESCRIPTION:
-- ~ Test of AS3 tree 1, 2, and 3 (inner and outer tests).
-- ~ Test of V-tree from Blelloch P. 85
-- ~ Test of minimal vtree and binary tree of depth 2 with different roots.
-- ==
-- entry: test__undirected_vgraph_to_parents_full
-- compiled nobench input { 3i64 [1i64,1i64,2i64,2i64] [4i64, 3i64, 5i64,1i64, 0i64,2i64] }
-- output { [3i64,2i64,3i64,-1i64] }
-- compiled nobench input { 0i64 [2i64,2i64,1i64,1i64] [2i64,5i64, 0i64,4i64, 3i64, 1i64] }
-- output { [-1i64,0i64,1i64,0i64] }
-- compiled nobench input { 7i64 [1i64,1i64,3i64,1i64,1i64,2i64,1i64,4i64] [10i64, 11i64, 12i64,5i64,6i64, 3i64, 4i64, 13i64,9i64, 8i64, 0i64,1i64,2i64,7i64] }
-- output { [7i64,7i64,7i64,2i64,2i64,7i64,5i64,-1i64] }
-- compiled nobench input { 0i64 [4i64,1i64,1i64,3i64,1i64,1i64,2i64,1i64] [5i64,4i64,11i64,8i64, 1i64, 0i64, 9i64,10i64,3i64, 6i64, 7i64, 2i64,13i64,12i64] }
-- output { [-1i64,0i64,0i64,0i64,3i64,3i64,0i64,6i64] }
-- compiled nobench input { 2i64 [2i64,2i64,1i64,2i64,1i64] [4i64,2i64, 1i64,5i64, 0i64, 3i64,7i64, 6i64] }
-- output { [2i64,0i64,-1i64,1i64,3i64] }
-- compiled nobench input { 0i64 [1i64,2i64,2i64,2i64,1i64] [1i64, 0i64,4i64, 5i64,2i64, 3i64,7i64, 6i64] }
-- output { [-1i64,0i64,1i64,2i64,3i64] }
-- compiled nobench input { 5i64 [1i64,4i64,1i64,1i64,1i64,2i64] [8i64, 9i64,5i64,6i64,7i64, 2i64, 3i64, 4i64, 0i64,1i64] }
-- output { [5i64,5i64,1i64,1i64,1i64,-1i64] }
-- compiled nobench input { 0i64 [2i64,4i64,1i64,1i64,1i64,1i64] [2i64,9i64, 0i64,6i64,7i64,8i64, 3i64, 4i64, 5i64, 1i64] }
-- output { [-1i64,0i64,1i64,1i64,1i64,0i64] }
-- compiled nobench input { 1i64 [1i64,2i64,1i64] [1i64, 0i64,3i64, 2i64] }
-- output { [1i64,-1i64,1i64] }
-- compiled nobench input { 0i64 [1i64,2i64,1i64] [1i64, 0i64,3i64, 2i64] }
-- output { [-1i64,0i64,1i64] }
-- compiled nobench input { 2i64 [1i64,2i64,1i64] [1i64, 0i64,3i64, 2i64] }
-- output { [1i64,2i64,-1i64] }
-- compiled nobench input { 3i64 [1i64,1i64,3i64,2i64,3i64,1i64,1i64] [2i64, 3i64, 0i64,1i64,5i64, 4i64,7i64, 6i64,10i64,11i64, 8i64, 9i64] }
-- output { [2i64,2i64,3i64,-1i64,3i64,4i64,4i64] }
-- compiled nobench input { 0i64 [1i64,1i64,3i64,2i64,3i64,1i64,1i64] [2i64, 3i64, 0i64,1i64,5i64, 4i64,7i64, 6i64,10i64,11i64, 8i64, 9i64] }
-- output { [-1i64,2i64,0i64,2i64,3i64,4i64,4i64] }
