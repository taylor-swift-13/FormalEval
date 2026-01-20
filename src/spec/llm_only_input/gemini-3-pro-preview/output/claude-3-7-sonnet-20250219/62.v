Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.

(* Note: The specification has been adjusted to 'Definition' as it is not recursive.
   The index for 'ds' is adjusted to 'pred i' to match the mathematical definition of 
   a derivative (where the coefficient for x^i in xs corresponds to x^(i-1) in ds) 
   and the provided test case. *)
Definition derivative_spec (xs : list nat) (ds : list nat) : Prop :=
  length ds = pred (length xs) /\
  (forall i : nat, 1 <= i < length xs -> nth (pred i) ds 0 = nth i xs 0 * i).

Example test_derivative : derivative_spec [3; 1; 2; 4; 5] [1; 4; 12; 20].
Proof.
  unfold derivative_spec.
  split.
  - (* Check length *)
    simpl. reflexivity.
  - (* Check elements *)
    intros i [Hge Hlt].
    (* We analyze each specific index i *)
    destruct i.
    + (* i = 0: contradicts 1 <= i *)
      inversion Hge.
    + destruct i.
      * (* i = 1: nth 0 ds = nth 1 xs * 1 -> 1 = 1 * 1 *)
        simpl. reflexivity.
      * destruct i.
        -- (* i = 2: nth 1 ds = nth 2 xs * 2 -> 4 = 2 * 2 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 3: nth 2 ds = nth 3 xs * 3 -> 12 = 4 * 3 *)
              simpl. reflexivity.
           ++ destruct i.
              ** (* i = 4: nth 3 ds = nth 4 xs * 4 -> 20 = 5 * 4 *)
                 simpl. reflexivity.
              ** (* i >= 5: contradicts i < length xs (which is 5) *)
                 simpl in Hlt.
                 (* Reduce the inequality 5 <= i < 5 to False *)
                 repeat apply lt_S_n in Hlt.
                 inversion Hlt.
Qed.