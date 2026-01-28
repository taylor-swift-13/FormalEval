Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Open Scope string_scope.
Import ListNotations.

Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition count_upper_impl (s : string) : nat :=
  length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).

Definition problem_98_pre (s : string) : Prop := True.

Definition problem_98_spec (s : string) (output : nat) : Prop :=
  output = count_upper_impl s.

Example problem_98_example :
  problem_98_spec "AEIOOUaeiouBACDFGJzKLmnOPrsTxyAWYzz" 5.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length = 39 *)
  (* Indices 0 to 38 *)
  (* Evaluate filter condition per index: *)
  (* i=0: 'A', even, uppercase vowel -> true *)
  (* i=1: 'E', odd -> false *)
  (* i=2: 'I', even, uppercase vowel -> true *)
  (* i=3: 'O', odd -> false *)
  (* i=4: 'O', even, uppercase vowel -> true *)
  (* i=5: 'U', odd -> false *)
  (* i=6: 'a', even, lowercase -> false *)
  (* i=7: 'e', odd -> false *)
  (* i=8: 'i', even, lowercase -> false *)
  (* i=9: 'o', odd -> false *)
  (* i=10:'u', even, lowercase -> false *)
  (* i=11:'B', odd -> false *)
  (* i=12:'A', even, uppercase vowel -> true *)
  (* i=13:'C', odd -> false *)
  (* i=14:'D', even, uppercase not vowel -> false *)
  (* i=15:'F', odd -> false *)
  (* i=16:'G', even, uppercase not vowel -> false *)
  (* i=17:'J', odd -> false *)
  (* i=18:'z', even, lowercase -> false *)
  (* i=19:'K', odd -> false *)
  (* i=20:'L', even, uppercase not vowel -> false *)
  (* i=21:'m', odd -> false *)
  (* i=22:'n', even, lowercase -> false *)
  (* i=23:'O', odd -> false *)
  (* i=24:'P', even, uppercase not vowel -> false *)
  (* i=25:'r', odd -> false *)
  (* i=26:'s', even, lowercase -> false *)
  (* i=27:'T', odd -> false *)
  (* i=28:'x', even, lowercase -> false *)
  (* i=29:'y', odd -> false *)
  (* i=30:'A', even, uppercase vowel -> true *)
  (* i=31:'W', odd -> false *)
  (* i=32:'Y', even, uppercase not vowel -> false *)
  (* i=33:'z', odd -> false *)
  (* i=34:'z', even, lowercase -> false *)

  (* Filtered indices: 0,2,4,12,30 *)
  (* length = 5 *)

  reflexivity.
Qed.