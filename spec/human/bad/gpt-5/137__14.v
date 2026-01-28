Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

Definition is_digit (c : ascii) : bool :=
  ("0" <=? c)%char && (c <=? "9")%char.

Definition digit_val (c : ascii) : nat :=
  Nat.sub (nat_of_ascii c) (nat_of_ascii "0").

Fixpoint digits_to_nat (l : list ascii) (acc : nat) : option nat :=
  match l with
  | [] => Some acc
  | c :: tl => if is_digit c then
                 digits_to_nat tl (acc * 10 + digit_val c)
               else None
  end.

Definition is_sep (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 46 || Nat.eqb (nat_of_ascii c) 44.

Fixpoint split_on_sep (l : list ascii) : (list ascii * list ascii) :=
  match l with
  | [] => ([], [])
  | c :: tl => if is_sep c then ([], tl)
               else let (pre, suf) := split_on_sep tl in (c :: pre, suf)
  end.

Fixpoint pow10 (n : nat) : R :=
  match n with
  | 0%nat => 1%R
  | S n' => 10 * pow10 n'
  end.

Definition parse_string (s : string) : option (bool * nat * nat * nat) :=
  let l := list_ascii_of_string s in
  match l with
  | [] => None
  | c0 :: tl0 =>
    let (neg, rest) :=
      if Nat.eqb (nat_of_ascii c0) 45 then (true, tl0) (* '-' *)
      else if Nat.eqb (nat_of_ascii c0) 43 then (false, tl0) (* '+' *)
      else (false, l) in
    let (int_chars, frac_chars) := split_on_sep rest in
    match int_chars with
    | [] => None
    | _ =>
      match digits_to_nat int_chars 0 with
      | None => None
      | Some int_v =>
        match frac_chars with
        | [] => Some (neg, int_v, 0%nat, 0%nat)
        | _ => match digits_to_nat frac_chars 0 with
               | None => None
               | Some frac_v => Some (neg, int_v, frac_v, length frac_chars)
               end
        end
      end
    end
  end.

Definition str_represents (s : string) (r : R) : Prop :=
  match parse_string s with
  | None => False
  | Some (neg, int_v, frac_v, k) =>
      let base := (INR int_v + (if (k =? 0)%nat then 0 else INR frac_v / pow10 k))%R in
      if neg then r = - base else r = base
  end.

Inductive value_of_rel : val -> R -> Prop :=
  | vor_int : forall z, value_of_rel (VInt z) (IZR z)
  | vor_float : forall r, value_of_rel (VFloat r) r
  | vor_str : forall s r, str_represents s r -> value_of_rel (VStr s) r.

Inductive Rlt_bool_rel : R -> R -> bool -> Prop :=
  | rbr_lt : forall x y, Rlt x y -> Rlt_bool_rel x y true
  | rbr_ge : forall x y, ~ Rlt x y -> Rlt_bool_rel x y false.

Definition problem_137_pre (a b : val) : Prop := True.

Definition problem_137_spec (a b : val) (res : option val) : Prop :=
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel ra rb true /\
     res = Some b) \/
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel rb ra true /\
     res = Some a) \/
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel ra rb false /\
     Rlt_bool_rel rb ra false /\
     res = None).

Example test_problem_137 :
  problem_137_spec (VStr "5,000") (VInt 5000%Z) (Some (VInt 5000%Z)).
Proof.
  left.
  exists (5%R), (IZR 5000%Z).
  split.
  - apply vor_str.
    unfold str_represents.
    assert (parse_string "5,000" = Some (false, 5%nat, 0%nat, 3%nat)) by reflexivity.
    rewrite H.
    simpl.
    rewrite INR_0.
    unfold Rdiv.
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    reflexivity.
  - split.
    + apply vor_int.
    + split.
      * apply rbr_lt. apply IZR_lt. lia.
      * reflexivity.
Qed.