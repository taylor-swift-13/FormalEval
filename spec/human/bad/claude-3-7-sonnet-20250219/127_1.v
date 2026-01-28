Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope string_scope.

Definition problem_127_pre (i1 i2 : Z * Z) : Prop :=
  let '(s1,e1) := i1 in
  let '(s2,e2) := i2 in s1 <= e1 /\ s2 <= e2.

Definition problem_127_spec (i1 i2 : Z * Z) (output : string) : Prop :=
  let (s1, e1) := i1 in
  let (s2, e2) := i2 in

  let s_inter := Z.max s1 s2 in
  let e_inter := Z.min e1 e2 in

  if Z.leb s_inter e_inter then
    let len_z := e_inter - s_inter in
    let len_nat := Z.to_nat len_z in
    (* prime expects Z integer > 1 *)
    (prime (Z.of_nat len_nat) /\ output = "YES") \/
    (~prime (Z.of_nat len_nat) /\ output = "NO")
  else
    output = "NO".

Example example_intersection_1 :
  problem_127_spec (1, 2) (2, 3) "NO".
Proof.
  unfold problem_127_spec.
  (* Compute intersection *)
  (* s_inter = max 1 2 = 2 *)
  replace (Z.max 1 2) with 2 by reflexivity.
  (* e_inter = min 2 3 = 2 *)
  replace (Z.min 2 3) with 2 by reflexivity.
  (* s_inter <= e_inter? 2 <= 2, true *)
  rewrite Z.leb_le; lia.
  (* unfold if branch *)
  simpl.

  (* len_z = 2 - 2 = 0 *)
  replace (2 - 2) with 0 by lia.
  simpl.
  (* len_nat = Z.to_nat 0 = 0 *)
  replace (Z.to_nat 0) with 0%nat by reflexivity.
  simpl.

  (* Goal: (prime (Z.of_nat 0) /\ "NO" = "YES") \/ (~prime (Z.of_nat 0) /\ "NO" = "NO") *)
  right.
  split.
  - (* ~ prime 0 *)
    unfold prime.
    intros [Hgt _].
    lia.
  - reflexivity.
Qed.