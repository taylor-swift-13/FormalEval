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

Example problem_141_test_K_dll :
  problem_141_spec "K.dll"%string "Yes"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  left. split.
  - split.
    + vm_compute. lia.
    + exists (("K"::[])%char).
      exists (("d"::"l"::"l"::[])%char).
      split.
      * vm_compute. reflexivity.
      * split.
        { intro HIn.
          apply in_app_iff in HIn.
          destruct HIn as [Hin1|Hin2].
          - assert (~ In "."%char (("K"::[])%char)) as Hpref.
            { unfold not. intros H.
              simpl in H.
              destruct H as [HK|H]; [vm_compute in HK; discriminate|].
              contradiction.
            }
            apply Hpref in Hin1. contradiction.
          - assert (~ In "."%char (("d"::"l"::"l"::[])%char)) as Hsuf.
            { unfold not. intros H.
              simpl in H.
              destruct H as [Hd|H]; [vm_compute in Hd; discriminate|].
              simpl in H.
              destruct H as [Hl|H]; [vm_compute in Hl; discriminate|].
              simpl in H.
              destruct H as [Hl2|H]; [vm_compute in Hl2; discriminate|].
              contradiction.
            }
            apply Hsuf in Hin2. contradiction.
        }
        split.
        { exists ("K"%char).
          exists ([]%char).
          split; [reflexivity|].
          unfold is_alpha. right.
          vm_compute. split; lia.
        }
        { right. right. reflexivity. }
  - reflexivity.
Qed.