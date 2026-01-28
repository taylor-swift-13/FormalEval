Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope char_scope.

(* Helper function to convert string to list ascii *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* Inductive val defined before Pre to avoid "reference not found" error *)
Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

Definition Pre (a b : val) : Prop := True.

(* String parsing logic *)
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

(* Helper to convert string to R, fixing the type error in value_of_impl *)
Definition string_to_R (s : string) : R :=
  match parse_string s with
  | None => 0%R (* Fallback for invalid strings *)
  | Some (neg, int_v, frac_v, k) =>
      let base := (INR int_v + (if (k =? 0)%nat then 0 else INR frac_v / pow10 k))%R in
      if neg then (- base)%R else base
  end.

Definition value_of_impl (v : val) : R :=
  match v with
  | VInt z => IZR z
  | VFloat r => r
  | VStr s => string_to_R s
  end.

Definition Rlt_bool (x y : R) : bool :=
  match Rlt_dec x y with
  | left _ => true
  | right _ => false
  end.

Definition compare_one_impl (a b : val) : option val :=
  let ra := value_of_impl a in
  let rb := value_of_impl b in
  if Rlt_bool ra rb then Some b
  else if Rlt_bool rb ra then Some a
  else None.

Definition compare_one_spec (a b : val) (res : option val) : Prop :=
  res = compare_one_impl a b.

(* Test case: input = ["7.3"; -2.0%R], output = "7.3" *)
Example test_compare_one : compare_one_spec (VStr "7.3") (VFloat (-2.0)%R) (Some (VStr "7.3")).
Proof.
  unfold compare_one_spec, compare_one_impl.
  simpl.
  unfold Rlt_bool.
  destruct (Rlt_dec _ _) as [Hlt1 | Hnlt1].
  - (* Case 7.3 < -2.0: False *)
    exfalso. lra.
  - (* Case ~(7.3 < -2.0): True, continue to next check *)
    destruct (Rlt_dec _ _) as [Hlt2 | Hnlt2].
    + (* Case -2.0 < 7.3: True *)
      reflexivity.
    + (* Case ~(-2.0 < 7.3): False *)
      exfalso. lra.
Qed.