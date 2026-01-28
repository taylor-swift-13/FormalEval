Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Definition get_char (s : string) (n : nat) : ascii :=
  match String.get n s with
  | Some c => c
  | None => " "%char
  end.

Definition problem_38_spec (input output : string) : Prop :=
  String.length input = String.length output /\
  let n := ((String.length input / 3) * 3 - 1)%nat in
  let L := String.length input in
  forall i, i < L ->
    let out_char := get_char output i in
    ((i <= n) ->
       (((i + 1) mod 3 = 1 /\ out_char = get_char input (i + 2)) \/
        (((i + 1) mod 3 = 2 \/ (i + 1) mod 3 = 0) /\ out_char = get_char input (i - 1)))) /\
    (~(i <= n) -> out_char = get_char input i).

Definition input_38 := "uzfplzjfzcltmdly".
Definition output_38 := "fuzzplzjftcllmdy".

(* Helper lemma: get_char returns Some c when index in bounds *)
Lemma get_char_some_eq :
  forall s n c,
    (n < String.length s)%nat ->
    String.get n s = Some c ->
    get_char s n = c.
Proof.
  intros s n c Hlt Hget.
  unfold get_char.
  rewrite Hget.
  reflexivity.
Qed.

Example test_case_38 :
  problem_38_spec input_38 output_38.
Proof.
  unfold problem_38_spec.
  split.
  - reflexivity.
  - intros i Hi.
    set (L := String.length input_38).
    set (n := ((L / 3) * 3 - 1)%nat).
    set (out_c := get_char output_38 i).
    split.
    + intros Hle.
      remember ((i + 1) mod 3) as r eqn:Hr.
      destruct r eqn:?.
      * (* r = 0 *)
        right; split.
        -- unfold out_c, get_char.
           (* (i+1) mod 3 = 0 *)
           left.
           reflexivity.
        -- unfold out_c, get_char.
           (* Out char = input[i-1] *)
           assert (Hgt1: 1 <= i).
           { lia. }
           (* Show get_char output_38 i = get_char input_38 (i-1) *)
           assert (Hi0 : i < L) by assumption.
           (* Use String.get for both *)
           remember (String.get i output_38) as go.
           remember (String.get (i - 1) input_38) as gi.
           destruct go as [co|]; destruct gi as [ci|]; try discriminate.
           injection Heqgo; intros; subst co.
           injection Heqgi; intros; subst ci.
           apply get_char_some_eq with (c := ci); auto.
      * (* r = 1 *)
        left; split; [assumption|].
        unfold out_c, get_char.
        assert (Hi2: (i + 2) < L).
        { 
          unfold L, n in *.
          destruct L eqn:EL.
          - lia.
          - (* Since i <= n < L and n = (L/3)*3-1, L>=1 *)
            assert (Hdiv3 := Nat.div_le_lower_bound i 3 L).
            lia.
        }
        remember (String.get i output_38) as go.
        remember (String.get (i + 2) input_38) as gi.
        destruct go as [co|]; destruct gi as [ci|]; try discriminate.
        injection Heqgo; intros; subst co.
        injection Heqgi; intros; subst ci.
        apply get_char_some_eq with (c := ci); auto.
      * (* r = 2 *)
        right; split.
        -- right; left; reflexivity.
        -- unfold out_c, get_char.
           assert (Hgt1: 1 <= i).
           { lia. }
           assert (Hi0 : i < L) by assumption.
           remember (String.get i output_38) as go.
           remember (String.get (i - 1) input_38) as gi.
           destruct go as [co|]; destruct gi as [ci|]; try discriminate.
           injection Heqgo; intros; subst co.
           injection Heqgi; intros; subst ci.
           apply get_char_some_eq with (c := ci); auto.
    + (* Case i > n *)
      intros Hgt.
      unfold out_c, get_char.
      assert (Hi0 : i < L) by assumption.
      remember (String.get i output_38) as go.
      remember (String.get i input_38) as gi.
      destruct go as [co|]; destruct gi as [ci|]; try discriminate.
      injection Heqgo; intros; subst co.
      injection Heqgi; intros; subst ci.
      apply get_char_some_eq with (c := ci); auto.
Qed.