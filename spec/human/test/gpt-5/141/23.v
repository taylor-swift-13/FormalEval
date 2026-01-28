Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.
Import Nat.

Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char).

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n /\ n <= nat_of_ascii "z"%char) \/
  (nat_of_ascii "A"%char <= n /\ n <= nat_of_ascii "Z"%char).

Definition problem_141_pre (file_name : string) : Prop := True.

Definition problem_141_spec (file_name_str : string) (result : string) : Prop :=
  let file_name := list_ascii_of_string file_name_str in
  let is_valid :=
    (length (filter is_digit_bool file_name) <= 3) /\
    (exists prefix suffix,
      file_name = prefix ++ "."%char :: suffix /\
      ~ In "."%char (prefix ++ suffix) /\
      (exists first_char rest_prefix,
        prefix = first_char :: rest_prefix /\ is_alpha first_char) /\
      (suffix = ("t"::"x"::"t"::[])%char \/
       suffix = ("e"::"x"::"e"::[])%char \/
       suffix = ("d"::"l"::"l"::[])%char))
  in
  (is_valid /\ result = "Yes"%string) \/
  (~is_valid /\ result = "No"%string).

Example problem_141_test_final132 :
  problem_141_spec "final132"%string "No"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  right. split.
  - unfold not. intros Hvalid.
    destruct Hvalid as [Hdigits [prefix [suffix [Heq Hrest]]]].
    assert (~ In "."%char (("f"::"i"::"n"::"a"::"l"::"1"::"3"::"2"::[])%char)) as HnoDot.
    { unfold not. intro Hin.
      simpl in Hin.
      destruct Hin as [Hf|Hin]; [vm_compute in Hf; discriminate|].
      simpl in Hin.
      destruct Hin as [Hi|Hin]; [vm_compute in Hi; discriminate|].
      simpl in Hin.
      destruct Hin as [Hn|Hin]; [vm_compute in Hn; discriminate|].
      simpl in Hin.
      destruct Hin as [Ha|Hin]; [vm_compute in Ha; discriminate|].
      simpl in Hin.
      destruct Hin as [Hl|Hin]; [vm_compute in Hl; discriminate|].
      simpl in Hin.
      destruct Hin as [H1|Hin]; [vm_compute in H1; discriminate|].
      simpl in Hin.
      destruct Hin as [H3|Hin]; [vm_compute in H3; discriminate|].
      simpl in Hin.
      destruct Hin as [H2|Hin]; [vm_compute in H2; discriminate|].
      contradiction.
    }
    assert (In "."%char (("f"::"i"::"n"::"a"::"l"::"1"::"3"::"2"::[])%char)) as HdotIn.
    { rewrite Heq.
      apply in_app_iff. right.
      simpl. left. reflexivity.
    }
    apply HnoDot in HdotIn. contradiction.
  - reflexivity.
Qed.