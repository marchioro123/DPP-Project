
import "lib/github.com/diku-dk/cpprandom/random"

module rng_engine = minstd_rand
module rand_i32 = uniform_int_distribution i32 u32 rng_engine

--------------------------------------------------
-------------------- UTILITY----------------------
--------------------------------------------------

def step [n] (R: [n]i32) (S: [n]i64) =
    let f i = if S[i] == n
              then (R[i], S[i])
              else (R[i] + R[S[i]], S[S[i]])
    in unzip (tabulate n f)

def wyllie [n] (S: [n]i64) : [n]i32 =
    let R = replicate n 1
    let (R,_) = loop (R, S) for _i < 64 - i64.clz n do
                    step R S
    in R

def mkFlagArray 't [m] 
            (aoa_shp: [m]u32) (zero: t)     -- aoa_shp=[0,3,1,0,4,2,0]
            (aoa_val: [m]t)  
          : ([m]u32, []t) =                 -- aoa_val=[1,1,1,1,1,1,1]
  let shp_rot = map (\i->if i==0 then 0     -- shp_rot=[0,0,3,1,0,4,2]
                         else aoa_shp[i-1]
                    ) (iota m)
  let shp_scn = scan (+) 0 shp_rot          -- shp_scn=[0,0,3,4,4,8,10]
  let aoa_len = if m == 0 then 0i64         --aoa_len = 10
                else i64.u32 <|
                     shp_scn[m-1]+aoa_shp[m-1]
  let shp_ind = map2 (\shp ind ->           -- shp_ind= 
                       if shp==0 then -1i64 --  [-1,0,3,-1,4,8,-1]
                       else i64.u32 ind     -- scatter
                     ) aoa_shp shp_scn      --   [0,0,0,0,0,0,0,0,0,0]
  let r = scatter (replicate aoa_len zero)  --   [-1,0,3,-1,4,8,-1]
             shp_ind aoa_val                --   [1,1,1,1,1,1,1]
  in (shp_scn, r)                           -- r = [1,0,0,1,1,0,0,0,1,0]

def sgmScan 't [n] (op: t->t->t) (ne: t) 
                   (flg : [n]bool) (arr : [n]t) : [n]t =
  let flgs_vals =
    zip flg arr |>
    scan ( \ (f1, x1) (f2, x2) -> 
            let f = f1 || f2
            in  if f2 then (f, x2)
                else (f, op x1 x2) 
         ) (false,ne)
  let (_, vals) = unzip flgs_vals
  in vals

def find_index 'a [n] (p: a -> bool) (as: [n]a): i64 =
  let op (x, i) (y, j) =
    if x && y then if i < j
                   then (x, i)
                   else (y, j)
    else if y then (y, j)
    else (x, i)
  in (reduce_comm op (false, -1) (zip (map p as) (iota n))).1
  

--------------------------------------------------
----------------- BENCHMARKING -------------------
--------------------------------------------------

-- | Makes a flat (depth 1) parent tree in 
-- Euler tour format.
entry make_flat_parents (len: i64) : [len]i64 =
	(replicate len 0i64) with [0] = -1 

-- | Makes a chain (depth len-1) parent
-- tree in Euler tour format.
entry make_chain_parents (len: i64) =
	map (\i -> i-1) (iota len)

-- | Makes a full binary parent tree
-- in Euler tour format.
entry make_binary_parents (len: i64) : [len]i64 =
	let tree = 
		map (\i -> 
			if i % 2 == 1 then (i-1) / 2
			else i / 2
		) (iota (len-1))
	
	in [-1] ++ tree :> [len]i64

-- | Makes a general/random parent tree with no cycles.
entry random_parent_vector (seed: i32) (n: i64) : [n]i64 =
    let rngs = rng_engine.split_rng n (rng_engine.rng_from_seed [seed])
    in map2 (\i r -> if i == 0 then -1i64 
                     else i64.i32 (rand_i32.rand (0i32, i32.i64 (i-1i64)) r).1) (iota n) rngs
