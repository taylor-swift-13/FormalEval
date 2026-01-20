Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Fixpoint foldl_Z (f : Z -> Z -> Z) (acc : Z) (l : list Z) : Z :=
  match l with
  | nil => acc
  | x :: xs => foldl_Z f (f acc x) xs
  end.

Definition eval_digits (base : Z) (ds : list Z) : Z :=
  foldl_Z (fun acc d => acc * base + d) 0 ds.

Fixpoint string_of_digits (ds : list Z) : string :=
  match ds with
  | nil => EmptyString
  | d :: tl => String (ascii_of_nat (48 + Z.to_nat d)) (string_of_digits tl)
  end.

Definition digits_range (base : Z) (ds : list Z) : Prop :=
  Forall (fun t => 0 <= t /\ t < base) ds.

Definition change_base_spec (x base : Z) (ret : string) : Prop :=
  0 <= x /\ 2 <= base /\ base <= 9 /\
  (x = 0 /\ ret = String (ascii_of_nat 48) EmptyString \/
   x <> 0 /\ exists d ds,
     ret = string_of_digits (d :: ds) /\
     1 <= d /\ d < base /\
     digits_range base ds /\
     eval_digits base (d :: ds) = x).

Example test_change_base : change_base_spec 8 3 "22".
Proof.
  unfold change_base_spec.
  (* Verify bounds: 0 <= 8, 2 <= 3, 3 <= 9 *)
  split. { apply Z.leb_le; reflexivity. }
  split. { apply Z.leb_le; reflexivity. }
  split. { apply Z.leb_le; reflexivity. }
  
  (* Case x <> 0 *)
  right.
  split.
  { intro H. discriminate H. } (* 8 <> 0 *)
  
  (* Witness: digits are [2; 2]. Head is 2, tail is [2] *)
  exists 2. exists [2].
  
  (* Prove properties of witness *)
  split.
  { (* String generation: "22" *)
    simpl. reflexivity. 
  }
  split.
  { (* Leading digit >= 1 *)
    apply Z.leb_le; reflexivity. 
  }
  split.
  { (* Leading digit < base *)
    apply Z.ltb_lt; reflexivity. 
  }
  split.
  { (* Remaining digits in range *)
    unfold digits_range.
    constructor.
    - (* First element of tail: 2 *)
      split.
      + apply Z.leb_le; reflexivity.
      + apply Z.ltb_lt; reflexivity.
    - (* End of list *)
      constructor.
  }
  { (* Evaluation check: 2 * 3 + 2 = 8 *)
    unfold eval_digits.
    simpl.
    reflexivity.
  }
Qed.