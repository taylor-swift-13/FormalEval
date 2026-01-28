Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition space : ascii := Ascii.ascii_of_nat 32.

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition ends_with_single_letter_pred (s : string) : Prop :=
  let l := list_ascii_of_string s in
  exists pre c,
    l = pre ++ [c] /\
    is_alpha c /\
    (pre = [] \/ exists pre', pre = pre' ++ [space]).

Definition problem_134_spec (s : string) (b : bool) : Prop :=
  b = true <-> ends_with_single_letter_pred s.

(* lemma: last element of l = last element of l' ++ [d] = d *)
Lemma last_of_app_singleton : forall {A:Type} (l l': list A) (d:A),
  l = l' ++ [d] ->
  last l d = d.
Proof.
  intros A l l' d H.
  rewrite H.
  apply last_app_singleton.
Qed.

Example test_apple_false :
  problem_134_spec "apple" false.
Proof.
  unfold problem_134_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    unfold ends_with_single_letter_pred in H.
    simpl in H.
    remember [Ascii.ascii_of_nat 97; Ascii.ascii_of_nat 112; Ascii.ascii_of_nat 112; Ascii.ascii_of_nat 108; Ascii.ascii_of_nat 101] as l eqn:Hl.
    destruct H as [pre [c [Hl_eq [Halpha Hpre]]]].
    subst l.
    assert (c = Ascii.ascii_of_nat 101).
    {
      apply last_of_app_singleton with (l:=pre) (l':=pre) in Hl_eq.
      rewrite Hl_eq.
      reflexivity.
    }
    subst c.
    (* Now pre + [101] = whole list of length 5, so length pre = 4 *)
    destruct Hpre as [Hpre_empty | [pre' Hpre_eq]].
    + (* pre = [] impossible because total length is 5 *)
      simpl in Hl_eq.
      rewrite Hpre_empty in Hl_eq.
      discriminate.
    + (* pre = pre' ++ [space] *)
      (* pre last element is space *)
      assert (last pre space = space).
      {
        rewrite Hpre_eq.
        apply last_app_singleton.
      }
      (* Compute last pre by direct inspection *)
      (* pre corresponds to first 4 letters of "apple": a p p l *)
      (* last pre = ascii_of_nat 108 *)
      unfold space in *.
      (* ascii_of_nat 108 <> ascii_of_nat 32 *)
      injection 1 as H1.
      discriminate H1.
Qed.