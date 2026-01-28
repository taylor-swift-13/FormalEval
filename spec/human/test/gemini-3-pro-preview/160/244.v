Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* 此函数将字符形式的运算符解释为对应的二元整数运算。*)
Definition interp_op (op : ascii) : (Z -> Z -> Z) :=
  match op with
  | "+" % char => Z.add
  | "-" % char => Z.sub
  | "*" % char => Z.mul
  | "/" % char => Z.div
  | "^" % char => Z.pow
  | _ => fun _ _ => 0
  end.

(* 手动实现 find_index 函数。*)
Fixpoint find_index_aux {A} (p : A -> bool) (l : list A) (n : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if p x then Some n else find_index_aux p xs (S n)
  end.

Definition find_index {A} (p : A -> bool) (l : list A) : option nat :=
  find_index_aux p l 0.

(* 辅助函数，用于从列表末尾查找满足条件的第一个元素的索引。*)
(* Note: Using List.length explicitly to avoid conflict with String.length *)
Definition rfind_index {A} (p : A -> bool) (l : list A) : option nat :=
  match find_index p (rev l) with
  | Some i => Some ( (List.length l - 1) - i )%nat
  | None => None
  end.

(*
  核心的求值函数 - 辅助函数版本
*)
Fixpoint eval_helper (ops : list ascii) (nums : list Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0 (* 燃料耗尽，在正常逻辑下不应发生 *)
  | S fuel' => (* 还有燃料，继续执行 *)
      match nums with
      | [] => 0
      | [n] => n
      | _::_ =>
        match rfind_index (fun c => orb (Ascii.eqb c "+"%char) (Ascii.eqb c "-"%char)) ops with
        | Some i =>
            let op := nth i ops " "%char in
            interp_op op
              (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
              (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
        | None =>
            match rfind_index (fun c => orb (Ascii.eqb c "*"%char) (Ascii.eqb c "/"%char)) ops with
            | Some i =>
                let op := nth i ops " "%char in
                interp_op op
                  (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
                  (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
            | None =>
                match find_index (fun c => (Ascii.eqb c "^"%char)) ops with
                | Some i =>
                    let op := nth i ops " "%char in
                    interp_op op
                      (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
                      (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
                | None => 0
                end
            end
        end
      end
  end.

(*
  主求值函数
  它调用辅助函数，并提供初始燃料值，即操作数列表的长度。
*)
Definition eval (ops : list ascii) (nums : list Z) : Z :=
  eval_helper ops nums (List.length nums).

Definition do_algebra_impl (operators : string) (operands : list Z) : Z :=
  eval (list_ascii_of_string operators) operands.

(* 约束：
   - 操作符长度 = 操作数长度 - 1，且操作符至少1个、操作数至少2个
   - 操作数非负
   - 操作符仅限于 + - * / ^
*)
Definition problem_160_pre (operators : string) (operands : list Z) : Prop :=
  let ops := list_ascii_of_string operators in
  S (List.length ops) = List.length operands /\
  (1 <= List.length ops)%nat /\ (2 <= List.length operands)%nat /\
  Forall (fun z => 0 <= z) operands /\
  Forall (fun c => c = "+"%char \/ c = "-"%char \/ c = "*"%char \/ c = "/"%char \/ c = "^"%char) ops.

Definition problem_160_spec (operators : string) (operands : list Z) (result : Z) : Prop :=
  result = do_algebra_impl operators operands.

Example test_problem_160 : problem_160_spec "/-^^+" [10; 5; 2; 6; 5; 6] (-6445346696680782825416437566319089761637456833974531730775458184543286320283182271444696724454069038956845710516853679227391906314472525473605972032157139977579072274536639042609188424239239011508754703739045777656878358529704649968917973772632631547265108988673564340565414669050754107189934461209359173088009071057292182048207055511944321957631107582320769550273817437365425803616634744589768847406628195780833926069430597165954369780522749285621845574781238594256186903953861153303176896441658392575817676370529865789050949704491623251289858656430590799403111474069343311174729961703149302039829967343109506430902163853126226846299671207209843652715121060627707645328639969804594146255823707056928018553927401598448910817392258793829504109367951024355751777080090056862622346984774560976587957623743128115238602925503404340670688575287144521945780599246393041899381575385263083503362455788956808838972800128620297652599730863633054050090438583180834251017752933687059429621385942712776463461594548300808143636567774713596681273497730387423509577668208089024251510674662122432632162869668108587058231036051993177423888135796654318656178668928424648058848051792220086073932556880870287189856073831047955963229398581324101323231362238407743525921216178639759630863960474226981963192351867081978762519381048511502895225154417828433592413836524655836904676713984307823406569179981579147603605719854256521058621172913948212219490172881402521647067562490605538691785584359655383060639443319770538511630392607795855994239188562237591045172170524539916695587989171729234704669970852272933351060812646600238269804791572041061062461501928875344312783778465424827106948266395029882306697236807403393332813731759903371014973752286918973141942533857198916273437430179121966082098941430795643158448995160865252058185826864343164378893117772507107917168573251826491158682856722917102178012299493421142371212159974260697253467269858681739347420919886568774232587558428240114023772479534302834747399213924450634124374545524650721640211344540206968297272857957795161297483376612398654165419198925254600296174534137660467989108971096878378794687024368407062086940073182226762346459197778455449068509159527946121272321674354542956701803601978142689835979192731607207241265008765090796874283616201190465057777089656747003063774051497042738027862183211104731128)%Z.
Proof.
  unfold problem_160_spec.
  unfold do_algebra_impl.
  unfold eval.
  vm_compute.
  reflexivity.
Qed.