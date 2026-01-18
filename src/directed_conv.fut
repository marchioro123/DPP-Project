
import "helpers"
import "parents_conv"
import "lib/github.com/diku-dk/sorts/radix_sort"



--------------------------------------------------
------------------ CONVERSION --------------------
--------------------------------------------------

def directed_vgraph_to_vtree [n] [m] (S_out: [n]u32) (S_in: [n]u32) (cross_pointers: [m]i64) =
    let (_, flags) = mkFlagArray S_out 0 (iota n)
    let II1 = (sgmScan (+) 0 (map bool.i64 flags) flags :> [m]i64)

    let root = find_index (==0) S_in
    let edges = (map2 (\x y -> (x, y + i64.bool (y >= root))) II1 cross_pointers) ++ [(-1, root)]

    let parents = radix_sort_int_by_key (\p -> p.1) i64.num_bits i64.get_bit edges |> unzip |> (.0)
    in parents_to_vtree (parents)