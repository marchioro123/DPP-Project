
import "lib/github.com/diku-dk/sorts/radix_sort"
import "parents_conv"
import "directed_conv"
import "undirected_conv"





--------------------------------------------------
-------------------- TESTING ---------------------
--------------------------------------------------

entry test__parents_to_vtree_naive [n] (parents: [n]i64) = parents_to_vtree_naive parents
entry test__parents_to_vtree_improved [n] (parents: [n]i64) = parents_to_vtree_improved parents

-- ~~ DESCRIPTION:
-- ~ Test of AS3 tree 1, 2, and 3.
-- ~ Test of V-tree from Blelloch P. 85
-- == 
-- entry: test__parents_to_vtree_naive test__parents_to_vtree_improved
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




--------------------------------------------------
----------------- BENCHMARKING -------------------
--------------------------------------------------

entry flat_naive [n] (parents: [n]i64) = parents_to_vtree_naive parents
entry chain_naive [n] (parents: [n]i64) = parents_to_vtree_naive parents
entry binary_naive [n] (parents: [n]i64) = parents_to_vtree_naive parents

entry flat_improved [n] (parents: [n]i64) = parents_to_vtree_improved parents
entry chain_improved [n] (parents: [n]i64) = parents_to_vtree_improved parents
entry binary_improved [n] (parents: [n]i64) = parents_to_vtree_improved parents

entry random_improved [n] (parents: [n]i64) = parents_to_vtree_improved parents

-- ==
-- entry: flat_naive flat_improved
-- compiled notest input @ data/ps_flat_100.in
-- compiled notest input @ data/ps_flat_1000.in
-- compiled notest input @ data/ps_flat_10000.in
-- compiled notest input @ data/ps_flat_100000.in
-- compiled notest input @ data/ps_flat_1000000.in
-- compiled notest input @ data/ps_flat_10000000.in

-- ==
-- entry: chain_naive chain_improved
-- compiled notest input @ data/ps_chain_100.in
-- compiled notest input @ data/ps_chain_1000.in
-- compiled notest input @ data/ps_chain_10000.in
-- compiled notest input @ data/ps_chain_100000.in
-- compiled notest input @ data/ps_chain_1000000.in
-- compiled notest input @ data/ps_chain_10000000.in

-- ==
-- entry: binary_naive binary_improved
-- compiled notest input @ data/ps_binary_100.in
-- compiled notest input @ data/ps_binary_1000.in
-- compiled notest input @ data/ps_binary_10000.in
-- compiled notest input @ data/ps_binary_100000.in
-- compiled notest input @ data/ps_binary_1000000.in
-- compiled notest input @ data/ps_binary_10000000.in

-- ==
-- entry: random_improved
-- compiled notest input @ data/ps_random_100.in
-- compiled notest input @ data/ps_random_1000.in
-- compiled notest input @ data/ps_random_10000.in
-- compiled notest input @ data/ps_random_100000.in
-- compiled notest input @ data/ps_random_1000000.in
-- compiled notest input @ data/ps_random_10000000.in