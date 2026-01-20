
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition nonempty_subarray (l : list Z) (sub : list Z) : Prop :=
  exists i j,
    0 <= i <= j < length l /\
    sub = firstn (j - i + 1) (skipn i l).

Definition minSubArraySum_spec (nums : list Z) (res : Z) : Prop :=
  res = fold_left Z.min (map (fun sub => fold_left Z.add sub 0) 
                (filter (fun sub => existsb (fun _ => true) sub) (* non-empty check *)
                        (filter (fun sub => existsb (fun _ => true) sub) (* placeholder *)
                                (let subs := 
                                   (* all subarrays *) in []))) 0
         (* re-express below *) /\
  (* actual minimal sum over all non-empty subarrays *)
  res = fold_left Z.min
          (map (fun sub =>
            fold_left Z.add sub 0)
           (filter (fun sub =>
             exists (i j : nat), 
               0 <= i <= j < length nums /\
               sub = firstn (S (j - i)) (skipn i nums))
             (let subs := 
               flat_map (fun i => 
                 map (fun j => firstn (S (j - i)) (skipn i nums)) 
                     (seq i (length nums - i)))
             (seq 0 (length nums))) 
           )) 
           (hd 0 [])).

(* Simplified and cleaned version below *)

Definition all_nonempty_subarrays (l : list Z) : list (list Z) :=
  flat_map (fun i =>
    map (fun j => firstn (S (j - i)) (skipn i l)) 
        (seq i (length l - i))) (seq 0 (length l)).

Definition minSubArraySum_spec (nums : list Z) (res : Z) : Prop :=
  res = fold_left Z.min
          (map (fun sub => fold_left Z.add sub 0) (all_nonempty_subarrays nums))
          (hd 0 (map (fun sub => fold_left Z.add sub 0) (all_nonempty_subarrays nums))).
