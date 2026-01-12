-- ~~ TODO:

-- ~ Perform dept and subtree finding simultaneously within the same list-ranking.

-- ~ Polish undirected_grapth-parents convertion:
--   Change root-pointer to '-1'.
--   Convert further to vtree (with polymorphich method).
--   Comment, analyze and test.

-- ~ Write explicit return types for functions


-- ~~ NOTES:

-- ~ Parent vector -1 root pointer:
--   To simplify code we have let the root pointer be -1 as opposed to self-referencing
--   pointer.

-- ~ Naive conversion version:
--   Assumes Euler tour of tree. Need for slow computatipn of subtree sizes.
--   Simple and efficient if tree given in Euler tour and subtree sizes already known.

-- ~ Polymorphic subtree sizes <Fixed: now uses advanced method>:
--   Used the naive/inefficient version at hand. Made function polymorphic as input
--   parameter to allow for a potentially faster version to be supplied (e.g. list-
--   ranking based or Williams idea with Blelloch's scan) 

-- ~ Validates:
--   Implementation validates on all three parent trees of AS3 and the example tree of
--   from Blelloch P. 85.


-- ~~ FURTHER IDEAS:

-- ~ Benchamrk compare Rasmus' and Martins' conversions on different backends and compared to each other.
-- ~ Benchmark differences between directed vs. undirected vgraph conversions <hard to random generate large trees>.

-- ~ Perform convertions BACK from vtree to parents or to vgraphs
-- ~ Perform advanced (unconstrained) conversion from undirected vgraph to parents.
-- ~ Implement the splitting and merging vtree operations.




import "helpers"



-- | 'find_depths' helper function.
-- Accumulates depth updates.
-- Work: O(n), Span: O(1)
def update_depths [n] (depths: [n]i64) (parents: [n]i64) 
			 : ([n]i64, [n]i64) =

	-- if completed or root: Do nothing.
	-- else: Add previous depth.
	let f i = if parents[i] == -1 || parents[i] == n
			  then (depths[i], parents[i])
			  else (depths[i] + depths[parents[i]], 
			  		parents[parents[i]])

	in unzip (tabulate n f)


-- | Computes the depth vector of a plain tree 
-- (given its parent vector with -1 root pointer)
-- through Wyllie-like list-ranking.
-- Work: O(n lg n), Span: O(lg n)
def find_depths [n] (parents: [n]i64) : [n]i64 =
	let depths = map (\p -> if p == -1 then 0 else 1) parents
		    	 -- ^^ initial depths (with root pointer of -1)

	let (depths, _) = -- (Wyllie ranking)
		loop (depths, parents)
		while any (\x -> x != -1) parents 
		do update_depths depths parents

	in depths


-- | Computes sub-tree sizes in a 
-- depth-wise manner (from the
-- deepest nodes to root)
-- - naive version.
-- Work: O(d * n), Span: O(d * n) <d: depth>
def subtree_sizes_naive [n] 
		(parents: [n]i64)
		(depts: [n]i64) =

	-- max depth
	let max_d = reduce i64.max 0 depts
	let sizes = replicate n 1

	-- iterates over all depths
	let (_, sizes') = 
		loop (d, sizes) = (max_d, sizes)
		while d >= 1 do
		
			-- finds elements of 
			-- current depth.
			let flgs = 
			map (\d_ -> 
				if d_ == d then true
				else false
			) depts
			
			-- negates parent indicies
			-- for parents with children
			-- of different depths.
			let ids =
			map2 (\f p ->
				if f then p else -1
			) flgs parents
			
			-- accumulates current subtree sums to parents 
			let prev = copy sizes
			let sizes' = reduce_by_index sizes (+) 0 ids prev
			in (d-1, sizes')

	in map i64.i32 sizes'


-- | Computes sub-tree sizes through
-- Wyllie list-ranking - advanced version.
--  Work: O(n lg n), Span: O(n lg n) (worst case)
--  Work: O(n lg n), Span: O(lg n) (practice)
def subtree_sizes_advanced [n] 
		(parents: [n]i64) (_: [n]i64) =

	let sizes = replicate n 1i64

	let (sizes, _) = -- (Wyllie ranking)
		loop (sizes, parents)
		while any (\x -> x != -1) parents do

			-- goes to parents
			let parents' =
					map (\p -> 
						if p == -1 then -1
						else parents[p]
					) parents

			-- accumulates size updates
			let sizes' = reduce_by_index sizes 
							(+) 0 parents (copy sizes)

			in  (sizes', parents')

	in sizes



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
def parents_to_vtree_naive [n] 
		(find_subtree_sizes: [n]i64 -> [n]i64 -> [n]i64)
		(parents: [n]i64) =

	-- depth of current and previous nodes
	let depths      = find_depths parents
	let depths_prev = rotate (-1) depths

	-- finds left-paren offsets through
	-- depths differences.
	let left_offsets = 
		map2 (\d_curr d_prev ->
			if d_curr == 0 then 0
			else d_prev - d_curr + 2
		) depths depths_prev
	
	let left_paren = scan (+) 0 left_offsets 

	-- computes left-parens through right-
	-- parens and subtree sizes.
	let sizes = find_subtree_sizes parents depths
	let right_paren = 
		map2 (\left size ->
			left + size * 2 - 1
		) left_paren sizes
	
	in (left_paren, right_paren)



--- TESTING ---

entry test__parents_to_vtree_naive [n] (parents: [n]i64) =
	parents_to_vtree_naive subtree_sizes_advanced parents

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



--- EXPERIMENTS ---

-- Constrained conversion. Assumes a graph with no cycles, where root node has a self-pointer. 
-- If euler_tour == true: Assumes parent pointers are always the first pointer in each segment.
-- If euler_tour == false: Assumes that parent nodes always precede their children (e.g. Euler Tour).
def undirected_vgraph_to_parents_constrained [m] [n] (euler_tour: bool) 
											 (vgraph: ([m]i64, [n]i64, [n]f32)) =
	let (segments, pointers, _) = vgraph 

	let (segs_start, segs_dist) = mkFlagArray (map u32.i64 segments) 0 (iota m) :> ([m]u32, [n]i64)
	let flags = map bool.i64 segs_dist with [0] = true
	let segs_start = map i64.u32 segs_start -- B1 array

	let po_seg = sgmScan (+) 0 flags segs_dist -- II1
	let po_segstart = scatter (replicate n 0) segs_start segs_start |> sgmScan (+) 0 flags
	let po_order = sgmScan (+) 0 flags (replicate n 1) |> map (\i -> i-1) -- II2 <better method in slides>
	let segment_offsets = [1] ++ (init segments) |> scan (\s1 s2 -> s1 + s2 - 1) 0

	let pointers_norm = map (\p -> p - po_order[p]) pointers
	let po_flgs_ids = zip3 pointers_norm flags (iota n)

	let (pointer_ps, _, _) =
		if euler_tour
		then 
			filter (\(p, _, i) -> p <= po_segstart[i])
				po_flgs_ids :> [m](i64, bool, i64)
		else 
			filter (\(_, f, _) -> f)
				po_flgs_ids :> [m](i64, bool, i64)
		|> unzip3

	in map (\i -> 
		let segment = po_seg[pointer_ps[i]]
		in if segment == i then -1
		   else pointer_ps[i] - segment_offsets[segment]
	) (indices pointer_ps)



-- Unconstrained conversion. Assumes a fully connected graph with no cycles. 
-- 'root' given as index of root node in 'segments' array.
def undirected_vgraph_to_parents_full [m] [n] (root: i64)
									  (vgraph: ([m]i64, [n]i64, [m]f32)) =
	
	let (segments, pointers, _) = vgraph

	let (segs_start, segs_dist) = mkFlagArray (map u32.i64 segments) 0 (iota m) :> ([m]u32, [n]i64)
	let flags = map bool.i64 segs_dist with [0] = true
	let segs_start = map i64.u32 segs_start -- B1 array

	let po_seg = sgmScan (+) 0 flags segs_dist -- II1 
	let po_active = map (\p -> p == root) po_seg
	let po_ids = map2 (\p a -> if a then p else -1) pointers po_active
	let po_parents = replicate n false

	let (po_parents', _) =
		loop (po_parents, po_ids)
		while any (\p -> p != -1) po_ids do

			let po_parents' = scatter po_parents po_ids (replicate n true)
			let seg_ids = map (\p -> if p == -1 then -1 else po_seg[p]) po_ids
			let segs_active = scatter (replicate m false) seg_ids (replicate n true)
			let po_ids' = map2 (\i ps -> if segs_active[po_seg[i]] && not ps then pointers[i] else -1) (iota n) po_parents'

			in (po_parents', po_ids')
		
	let po_parents'' = po_parents' with [segs_start[root]] = true
	let po_order = sgmScan (+) 0 flags (replicate n 1) |> map (\i -> i-1) -- II2 <better method in slides>
	let seg_offs = [1] ++ (init segments) |> scan (\s1 s2 -> s1 + s2 - 1) 0

	let pointers_norm = map (\p -> p - po_order[p]) pointers
	let (parents_, _) = zip pointers_norm po_parents'' |> filter (\(_, ps) -> ps) |> unzip :> ([m]i64, [m]bool)

	in map (\i -> 
		let seg = po_seg[parents_[i]]
		in parents_[i] - seg_offs[seg]
	) (iota m) with [root] = -1

	-- test (binary tree of depth 2):   undirected_vgraph_to_parents_full 3 ([1,1,3,2,3,1,1], [2, 3, 0,1,5, 4,7, 6,10,11, 8, 9], (replicate 7 0))
	-- test (minimal tree):             undirected_vgraph_to_parents_full 1 ([1,2,1], [1,0,3,2], (replicate 3 0))







--- OLD

-- -- | depth helper function. 
-- -- Accumulates depth updates.
-- -- Work: O(n), Span: O(1)
-- def step [n] (R: [n]i64) (parents: [n]i64) 
-- 			 (completed: [n]bool) 
-- 			 : ([n]i64, [n]i64) =

-- 	-- if completed or root: Do nothing.
-- 	-- else: Add previous depth.
-- 	let f i = if completed[i] || parents[i] == n
-- 			  then (R[i], parents[i])
-- 			  else (R[i] + R[parents[i]], 
-- 			  		parents[parents[i]])

-- 	in unzip (tabulate n f)


-- -- | Computes the depth vector of a plain tree 
-- -- (given its parent vector) through Wyllie-like
-- -- list-ranking.
-- -- Work: O(n lg n), Span: O(lg n)
-- def depth [n] (parents: [n]i64) : [n]i64 =
-- 	let R = replicate n 1 with [0] = 0
-- 		 -- ^^ initial depth (with root of 0)

-- 	-- completion status
-- 	-- of ranked sublist.
-- 	let completed =
-- 		map (\s ->
-- 			if s == 0 then true
-- 			else false
-- 		) parents

-- 	let (R, _, _) = -- (Wyllie list-ranking)
-- 		loop (R, parents, completed)
-- 		while not (reduce (&&) true completed)
-- 		do -- ^^ some sub-lists not completed

-- 			-- performs step and
-- 			-- evals sub-list completion
-- 			let (R', parents') = step R parents completed
-- 			let completed =
-- 				map (\p ->
-- 					if p == 0 then true
-- 					else false
-- 				) parents'

-- 			in  (R', parents', completed)

-- 	in R



	-- in zip parents' (indices parents')
	--    |> map (\(p, i) -> if II1[p] == i then -1 else p - parent_offsets[II1[p]])