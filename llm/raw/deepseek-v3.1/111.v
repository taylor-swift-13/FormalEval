
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedType.

Module StringOT <: OrderedType.
  Definition t := string.
  Definition eq := @eq string.
  Definition lt := String.lt.
  Definition eq_refl := @eq_refl string.
  Definition eq_sym := @eq_sym string.
  Definition eq_trans := @eq_trans string.
  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. apply String.lt_trans. Qed.
  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. intros x y H. apply String.lt_strorder; auto. Qed.
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof. intros s1 s2. destruct (String.compare s1 s2) eqn:H.
         - apply EQ; auto.
         - apply LT; auto.
         - apply GT; auto.
  Defined.
  Definition eq_dec := string_dec.
End StringOT.

Module StringMap := FMapWeakList.Make(StringOT).
Module StringMapFacts := WFacts_fun StringOT StringMap.

Definition histogram_spec (test : string) (result : StringMap.t nat) : Prop :=
  let words := filter (fun s => negb (String.eqb s "")) (String.split " " test) in
  let counts := fold_right (fun word m => 
                StringMap.update word (fun n => Some (S (match n with Some k => k | None => 0 end))) m)
                (StringMap.empty nat) words in
  let max_count := fold_right (fun c m => max m c) 0 (StringMap.values counts) in
  StringMap.Equal result (StringMap.filter (fun _ c => c =? max_count) counts) /\
  (words = nil -> StringMap.is_empty result).
