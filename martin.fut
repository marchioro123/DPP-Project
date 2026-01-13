import "lib/github.com/diku-dk/sorts/radix_sort"
import "lib/github.com/diku-dk/cpprandom/random"
import "helpers"

module rng_engine = minstd_rand
module rand_i32 = uniform_int_distribution i32 u32 rng_engine

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

def directed_vgraph_to_vtree [n] [m] (S_out: [n]u32) (S_in: [n]u32) (cross_pointers: [m]i64) =
    let (_, flags) = mkFlagArray S_out 0 (iota n)
    let II1 = (sgmScan (+) 0 (map bool.i64 flags) flags :> [m]i64)

    let root = find_index (==0) S_in
    let edges = (map2 (\x y -> (x, y + i64.bool (y >= root))) II1 cross_pointers) ++ [(-1, root)]

    let parents = radix_sort_int_by_key (\p -> p.1) i64.num_bits i64.get_bit edges |> unzip |> (.0)
    in parents_to_vtree (parents)

def undirected_vgraph_to_vtree [n] [m] (S: [n]u32) (cross_pointers: [m]i64) (root: i64) =
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
    in parents_to_vtree (parents)

def random_parent_vector (seed: i32) (n: i64) : [n]i64 =
    let rngs = rng_engine.split_rng n (rng_engine.rng_from_seed [seed])
    in map2 (\i r -> if i == 0 then -1i64 
                     else i64.i32 (rand_i32.rand (0i32, i32.i64 (i-1i64)) r).1) (iota n) rngs


-- parents_to_vtree [-1,0,0]
-- parents_to_vtree [-1,0,0,1]
-- parents_to_vtree [-1,0,0,0,1]
-- parents_to_vtree [2,2,4,2,-1]
-- parents_to_vtree [-1,0,1,1,1,0]

-- directed_vgraph_to_vtree [2,0,0] [0,1,1] [0,1]
-- directed_vgraph_to_vtree [2,1,0,0] [0,1,1,1] [0,1,2]
-- directed_vgraph_to_vtree [3,1,0,0,0] [0,1,1,1,1] [0,1,2,3]
-- directed_vgraph_to_vtree [0,0,3,0,1] [1,1,1,1,0] [0,1,3,2]
-- directed_vgraph_to_vtree [2,3,0,0,0,0] [0,1,1,1,1,1] [0,4,1,2,3]

-- undirected_vgraph_to_vtree [3,2,1,1,1] [3,5,6,0,7,1,2,4] 0