
import "helpers"
import "lib/github.com/diku-dk/sorts/radix_sort"



--------------------------------------------------
--------------- NAIVE CONVERSION -----------------
--------------------------------------------------

-- | Computes the depths and subtree sizes of a
-- parent tree using Wyllie list ranking.
-- Work: O(n * lg n), Span: O(n * lg n) (worst case)
-- Work: O(n * lg n), Span: O(lg n) (practice)
def wyllie_ds [n] (parents: [n]i64) =

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
				(iota n) :> [n]i64

			-- accumulates size updates
			let sizes = reduce_by_index sizes_ (+) 0 parents (copy sizes_)

			-- updates parents
			let parents' =
				map (\p -> 
					if p == -1 then -1
					else parents[p]
				) parents

			in  (sizes, depths, parents')
	
	in (depths, sizes) 


-- | Converts from plain tree (with parent
-- vector in Euler Tour form and root with
-- parent 0) to vtree.
-- Work: O(n * lg n), Span: O(n * lg n) (worst case)
-- Work: O(n * lg n), Span: O(lg n) (practice)
def parents_to_vtree_naive [n] (parents: [n]i64) =

	-- depth of current and previous nodes
	let (depths, sizes) = wyllie_ds parents
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
	let right_paren = 
		map2 (\left size ->
			left + size * 2 - 1
		) left_paren sizes
	
	in (left_paren, right_paren)



--------------------------------------------------
-------------- ADVANCED CONVERSION ---------------
--------------------------------------------------

def parents_to_vtree_improved [n] (parents: [n]i64) = -- assumes parent of root is -1
    let idxs = iota n
    let sort_by_parents = radix_sort_int_by_key (\p -> p.0) i64.num_bits i64.get_bit (zip parents idxs)

    -- first_child vector
    let (vs_parents, is) = 
        map2 (\(p1, i1) (p2, _) -> (if p1 != p2 then p1 else -1, i1)) sort_by_parents (rotate (-1) sort_by_parents) 
        |> unzip 
    let first_child = scatter (replicate n (-1)) vs_parents is

    -- next_sibling vector
    let (vs_siblings, is) = 
        map2 (\(p1, i1) (p2, i2) -> (if p1 == p2 then i2 else -1, i1)) sort_by_parents (rotate (1) sort_by_parents) 
        |> unzip 
    let next_sibling = scatter (replicate n (-1)) is vs_siblings

    -- Euler tour & list ranking
    let enter_succ = map2 (\i c -> if c != -1 then c else n+i) idxs first_child
    let exit_succ = map2 (\p s -> if s != -1 then s 
                                  else if p != -1 then n+p 
                                  else 2*n) parents next_sibling
    let ranks = map (2*i32.i64 n-) (wyllie (enter_succ ++ exit_succ))
			    |> map i64.i32

    in (ranks[0:n], ranks[n:2*n])