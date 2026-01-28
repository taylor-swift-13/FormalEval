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
  problem_98_spec
    "zAEIOUaeiouBCDFGJKLmnOPrsTxyzAEIOUaeiouBCDjLmnOPCrsOTxyzz" 5.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length = 63 *)
  (* indices from 0 to 62 *)
  (* Evaluate filter predicate on each index: *)
  (* i=0: "z", even true, is_uppercase_vowel_bool false -> false *)
  (* i=1: "A", even false -> false *)
  (* i=2: "E", even true, vowel true -> true *)
  (* i=3: "I", even false -> false *)
  (* i=4: "O", even true, vowel true -> true *)
  (* i=5: "U", even false -> false *)
  (* i=6: "a", even true, vowel false -> false *)
  (* i=7: "e", even false -> false *)
  (* i=8: "i", even true, vowel false -> false *)
  (* i=9: "o", even false -> false *)
  (* i=10:"u", even true, vowel false -> false *)
  (* i=11:"B", even false -> false *)
  (* i=12:"C", even true, vowel false -> false *)
  (* i=13:"D", even false -> false *)
  (* i=14:"F", even true, vowel false -> false *)
  (* i=15:"G", even false -> false *)
  (* i=16:"J", even true, vowel false -> false *)
  (* i=17:"K", even false -> false *)
  (* i=18:"L", even true, vowel false -> false *)
  (* i=19:"m", even false -> false *)
  (* i=20:"n", even true, vowel false -> false *)
  (* i=21:"O", even false -> false *)
  (* i=22:"P", even true, vowel false -> false *)
  (* i=23:"r", even false -> false *)
  (* i=24:"s", even true, vowel false -> false *)
  (* i=25:"T", even false -> false *)
  (* i=26:"x", even true, vowel false -> false *)
  (* i=27:"y", even false -> false *)
  (* i=28:"z", even true, vowel false -> false *)
  (* i=29:"A", even false -> false *)
  (* i=30:"E", even true, vowel true -> true *)
  (* i=31:"I", even false -> false *)
  (* i=32:"O", even true, vowel true -> true *)
  (* i=33:"U", even false -> false *)
  (* i=34:"a", even true, vowel false -> false *)
  (* i=35:"e", even false -> false *)
  (* i=36:"i", even true, vowel false -> false *)
  (* i=37:"o", even false -> false *)
  (* i=38:"u", even true, vowel false -> false *)
  (* i=39:"B", even false -> false *)
  (* i=40:"C", even true, vowel false -> false *)
  (* i=41:"D", even false -> false *)
  (* i=42:"j", even true, vowel false -> false *)
  (* i=43:"L", even false -> false *)
  (* i=44:"m", even true, vowel false -> false *)
  (* i=45:"n", even false -> false *)
  (* i=46:"O", even true, vowel true -> true *)
  (* i=47:"P", even false -> false *)
  (* i=48:"C", even true, vowel false -> false *)
  (* i=49:"r", even false -> false *)
  (* i=50:"s", even true, vowel false -> false *)
  (* i=51:"O", even false -> false *)
  (* i=52:"T", even true, vowel false -> false *)
  (* i=53:"x", even false -> false *)
  (* i=54:"y", even true, vowel false -> false *)
  (* i=55:"z", even false -> false *)
  (* i=56:"z", even true, vowel false -> false *)
  (* So indices contributing are 2,4,30,32,46 *)
  reflexivity.
Qed.