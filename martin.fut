import "lib/github.com/diku-dk/sorts/radix_sort"
import "helpers"

def parents_to_vtree [n] (parents: [n]i64) = -- assumes parent of root is -1
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

    in (ranks[0:n], ranks[n:2*n])

-- parents_to_vtree [-1,0,0]
-- parents_to_vtree [-1,0,0,1]
-- parents_to_vtree [-1,0,1,1,1,0]

def directed_vgraph_to_vtree [n] [m] (S_out: [n]u32) (cross_pointers: [m]i64) = -- assumes no cycles and root at index 0
    let (_, flags) = mkFlagArray S_out 0 (iota n)
    let II1 = (sgmScan (+) 0 (map bool.i64 flags) flags :> [m]i64)

    let edges = map2 (\x y -> (x+1, y)) cross_pointers II1
    let parents = radix_sort_int_by_key (\p -> p.0) i64.num_bits i64.get_bit edges |> unzip |> (.1)

    in parents_to_vtree ([-1] ++ parents)

-- directed_vgraph_to_vtree [2,0,0] [0,1]
-- directed_vgraph_to_vtree [2,1,0,0] [0,1,2]
-- directed_vgraph_to_vtree [2,3,0,0,0,0] [0,4,1,2,3]