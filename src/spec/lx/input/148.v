(* def bf(planet1, planet2):
'''
There are eight planets in our solar system: the closerst to the Sun
is Mercury, the next one is Venus, then Earth, Mars, Jupiter, Saturn,
Uranus, Neptune.
Write a function that takes two planet names as strings planet1 and planet2.
The function should return a tuple containing all planets whose orbits are
located between the orbit of planet1 and the orbit of planet2, sorted by
the proximity to the sun.
The function should return an empty tuple if planet1 or planet2
are not correct planet names.
Examples
bf("Jupiter", "Neptune") ==> ("Saturn", "Uranus")
bf("Earth", "Mercury") ==> ("Venus")
bf("Mercury", "Uranus") ==> ("Venus", "Earth", "Mars", "Jupiter", "Saturn")
''' *)
(* 引入必要的 Coq 库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Import ListNotations.

(* 定义行星名称为 list ascii，并按与太阳的距离排序 *)
Definition solar_system : list (list ascii) :=
  [
    ["M"%char; "e"%char; "r"%char; "c"%char; "u"%char; "r"%char; "y"%char];  (* Mercury *)
    ["V"%char; "e"%char; "n"%char; "u"%char; "s"%char];            (* Venus *)
    ["E"%char; "a"%char; "r"%char; "t"%char; "h"%char];            (* Earth *)
    ["M"%char; "a"%char; "r"%char; "s"%char];                (* Mars *)
    ["J"%char; "u"%char; "p"%char; "i"%char; "t"%char; "e"%char; "r"%char];  (* Jupiter *)
    ["S"%char; "a"%char; "t"%char; "u"%char; "r"%char; "n"%char];      (* Saturn *)
    ["U"%char; "r"%char; "a"%char; "n"%char; "u"%char; "s"%char];      (* Uranus *)
    ["N"%char; "e"%char; "p"%char; "t"%char; "u"%char; "n"%char; "e"%char]   (* Neptune *)
  ].

(* 辅助函数：定义一个用于比较两个 list ascii 是否相等的布尔函数 *)
Fixpoint list_ascii_eqb (l1 l2 : list ascii) : bool :=
  match l1, l2 with
  | [], [] => true
  | a1 :: t1, a2 :: t2 => if Ascii.eqb a1 a2 then list_ascii_eqb t1 t2 else false
  | _, _ => false
  end.

(* 辅助函数：获取一个行星在 solar_system 列表中的索引 (位置) *)
Fixpoint get_planet_index_aux (p_name : list ascii) (planets : list (list ascii)) (current_idx : nat) : option nat :=
  match planets with
  | [] => None
  | p :: ps => if list_ascii_eqb p p_name
               then Some current_idx
               else get_planet_index_aux p_name ps (S current_idx)
  end.

Definition get_planet_index (p_name : list ascii) : option nat :=
  get_planet_index_aux p_name solar_system 0.

(*
  bf 函数的程序规约 (Spec)
  - 输入: planet1 (list ascii), planet2 (list ascii)
  - 输出: result (list (list ascii))
*)
Definition bf_spec (planet1 planet2 : list ascii) (result : list (list ascii)) : Prop :=
  match (get_planet_index planet1), (get_planet_index planet2) with
  | Some idx1, Some idx2 =>
    (* --- 情况 1: planet1 和 planet2 都是有效的行星名称 --- *)
    let min_idx := min idx1 idx2 in
    let max_idx := max idx1 idx2 in
    
    (* 属性 1: 输出列表 `result` 中的每个行星 `p`，当且仅当 `p` 的轨道
       位置在 `planet1` 和 `planet2` 的轨道之间。*)
    (forall p, In p result <->
      (exists idx, get_planet_index p = Some idx /\
                   min_idx < idx < max_idx))
    /\
    (* 属性 2: 输出列表 `result` 必须是根据与太阳的距离排序的。*)
    (forall p_a p_b i j,
      nth_error result i = Some p_a ->
      nth_error result j = Some p_b ->
      i < j ->
      (exists idx_a idx_b,
         get_planet_index p_a = Some idx_a /\
         get_planet_index p_b = Some idx_b /\
         idx_a < idx_b))

  | _, _ =>
    (* --- 情况 2: planet1 或 planet2 不是有效的行星名称 --- *)
    (* 输出 `result` 必须为空列表。*)
    result = []
  end.