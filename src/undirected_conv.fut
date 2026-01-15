
import "lib/github.com/diku-dk/sorts/radix_sort"
import "helpers"
import "parents_conv"

type constraint = #inner | #outer | #full



--------------------------------------------------
-------------- NAIVE IMPLEMENTATION --------------
--------------------------------------------------

-- | Filters and normalizes the pointers
-- of an undirected 'vgraph' given an array
-- of boolean predicates 'po_parents'.
-- Work: O(n), Span: O(lg n).
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
-- Work: O(n), Span: O(lg n).
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
-- Work: O(n), Span: O(lg n).
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
-- Work: O(d * n), Span: O(d * lg n) <d: tree depth>.
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



-- | Converts from an undirected graph to a parents array
-- given constraint type and parents conversion function.
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




--------------------------------------------------
------------ IMPROVED IMPLEMENTATION -------------
--------------------------------------------------

def undirected_vgraph_to_vtree_improved [n] [m] (S: [n]u32) (cross_pointers: [m]i64) (root: i64) =
    let idxs = iota n
    let (_, flags) = mkFlagArray S 0 idxs
    let II1 = (sgmScan (+) 0 (map bool.i64 flags) flags :> [m]i64)

    let edges = zip (map (\x -> II1[x]) cross_pointers) II1
    let filtered_edges = (filter (\(x,y) -> x > y) edges :> [m/2](i64, i64))

    let (directed_edges, _) =
        loop (edges', visited) = (filtered_edges, map (==root) idxs)
        while any (==false) visited do
            let updated_edges = map (\(x,y) -> if !visited[x] && visited[y] then (y,x) else (x,y)) edges'
            let is = map (\(x,y) -> if visited[x] then y else -1) updated_edges
            in (updated_edges, scatter visited is (replicate (m/2) true))
    
    let parents = radix_sort_int_by_key (\p -> p.1) i64.num_bits i64.get_bit (directed_edges ++ [(-1, root)]) 
                  |> unzip |> (.0)
    in parents_to_vtree_improved (parents)




--------------------------------------------------
--------------- (INLINED FUNCTIONS) --------------
--------------------------------------------------

def parents_to_vtree_naive' [n] (parents: [n]i64) =

	let sizes_ = replicate n 1i64
	let depths_ = map (\p -> if p == -1 then 0 else 1) parents

	let (sizes, depths, _) =
		loop (sizes_, depths_, parents)
		while any (\x -> x != -1) parents do

			let depths = 
				map (\i -> 
					if parents[i] == -1 then depths_[i] 
					else depths_[i] + depths_[parents[i]]) 
				(iota n)

			let sizes = reduce_by_index sizes_ (+) 0 parents (copy sizes_)

			let parents' =
				map (\p -> 
					if p == -1 then -1
					else parents[p]
				) parents

			in  (sizes, depths, parents')	

	let depths_prev = rotate (-1) depths
	let left_offsets = 
		map2 (\d_curr d_prev ->
			if d_curr == 0 then 0
			else d_prev - d_curr + 2
		) depths depths_prev
	
	let left_paren = scan (+) 0 left_offsets 

	let right_paren = 
		map2 (\left size ->
			left + size * 2 - 1
		) left_paren sizes
	
	in (left_paren, right_paren)



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

