-- ~~ TODO:

-- ~ Homogonize parent vector form (with consistent -1 or 0 as root pointer)
--	 Currently 0 in Rasmus' and -1 in Martins version.


-- ~~ NOTES:

-- ~ Naive conversion version:
--   Assumes Euler tour of tree. Need for slow computatipn of subtree sizes.
--   Simple and efficient if tree given in Euler tour and subtree sizes already known.

-- ~ Polymorphic subtree sizes:
--   Used the naive/inefficient version at hand. Made function polymorphic as input
--   parameter to allow for a potentially faster version to be supplied (e.g. list-
--   ranking based or Williams idea with Blelloch's scan) 

-- ~ Validates:
--   Implementation validates on all three parent trees of AS3 and the example tree of
--   from Blelloch P. 85.



-- | depth helper function. 
-- Accumulates depth updates.
-- Work: O(n), Span: O(1)
def step [n] (R: [n]i64) (parents: [n]i64) 
			 (completed: [n]bool) 
			 : ([n]i64, [n]i64) =

	-- if completed or root: Do nothing.
	-- else: Add previous depth.
	let f i = if completed[i] || parents[i] == n
			  then (R[i], parents[i])
			  else (R[i] + R[parents[i]], 
			  		parents[parents[i]])

	in unzip (tabulate n f)


-- | Computes the depth vector of a plain tree 
-- (given its parent vector) through Wyllie-like
-- list-ranking.
-- Work: O(n lg n), Span: O(lg n)
def depth [n] (parents: [n]i64) : [n]i64 =
	let R = replicate n 1 with [0] = 0
		 -- ^^ initial depth (with root of 0)

	-- completion status
	-- of ranked sublist.
	let completed =
		map (\s ->
			if s == 0 then true
			else false
		) parents

	let (R, _, _) = -- (Wyllie list-ranking)
		loop (R, parents, completed)
		while not (reduce (&&) true completed)
		do -- ^^ some sub-lists not completed

			-- performs step and
			-- evals sub-list completion
			let (R', parents') = step R parents completed
			let completed =
				map (\p ->
					if p == 0 then true
					else false
				) parents'

			in  (R', parents', completed)

	in R


-- | Accumulates element sum for each subtree
-- in a depth-wise manner (from the deepest
-- nodes to root).
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



-- | Converts from plain tree (with parent
-- vector in Euler Tour form and root with
-- parent 0) to vtree.
--
-- ~~ Complexity <n: nodes, d: depth>
-- ~ general:
-- Work: O(n lg n  +  W(find_subtree_sizes)),
-- Span: O(lg n  +    S(find_subtree_sizes))
-- ~ with 'subtree_sizes_naive':
-- Work: O(n lg n + d * n),
-- Span: O(lg n +   d * n)
def parents_to_vtree_naive [n] 
		(find_subtree_sizes: [n]i64 -> [n]i64 -> [n]i64)
		(parents: [n]i64) =

	-- depth of current and previous nodes
	let depths      = depth parents
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
	parents_to_vtree_naive subtree_sizes_naive parents

-- ~~ DESCRIPTION:
-- ~ Test of AS3 tree 1, 2, and 3.
-- ~ Test of V-tree from Blelloch P. 85
-- == 
-- entry: test__parents_to_vtree_naive
-- compiled nobench input { [0i64, 0i64, 1i64, 0i64] }
-- output { [0i64, 1i64, 2i64, 5i64 ] [7i64, 4i64, 3i64, 6i64] }
-- compiled nobench input { [0i64, 0i64, 0i64, 0i64, 3i64, 3i64, 0i64, 6i64] }
-- output { [0i64, 1i64, 3i64, 5i64, 6i64, 8i64, 11i64, 12i64]
--			[15i64, 2i64, 4i64, 10i64, 7i64, 9i64, 14i64, 13i64] }
-- compiled nobench input { [0i64, 0i64, 1i64, 2i64, 3i64] }
-- output { [0i64, 1i64, 2i64, 3i64, 4i64] [9i64, 8i64, 7i64, 6i64, 5i64] }
-- compiled nobench input { [0i64, 0i64, 1i64, 1i64, 1i64, 0i64] }
-- output { [0i64, 1i64, 2i64, 4i64, 6i64, 9i64]
--			[11i64, 8i64, 3i64, 5i64, 7i64, 10i64] }