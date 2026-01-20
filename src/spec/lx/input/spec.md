## 6

![image-20250725112245900](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725112245900.png)

IsBalanced(g) ↔
  ∃ f : ℕ → ℤ,
    f(0) = 0 ∧
    ∀ i ∈ [0, |g|),
      (g[i] = '(' → f(i+1) = f(i) + 1) ∧
      (g[i] = ')' → f(i+1) = f(i) - 1) ∧
      (g[i] ≠ '(' ∧ g[i] ≠ ')' → f(i+1) = f(i)) ∧
    ∀ i ∈ [0, |g|], f(i) ≥ 0 ∧
    f(|g|) = 0

MaxNestingDepth(g, d) ↔
  ∃ f : ℕ → ℕ,
    ∀ i < |g|, 
      (g[i] = '(' → f(i+1) = f(i) + 1) ∧
      (g[i] = ')' → f(i+1) = f(i) - 1) ∧
      (g[i] ≠ '(' ∧ g[i] ≠ ')' → f(i+1) = f(i)) ∧
    f(0) = 0 ∧
    ∀ i ≤ |g|, f(i) ≥ 0 ∧
    d = max { f(i) | 0 ≤ i ≤ |g| }

ValidOutput(s, l) ↔
  ∃ n g₀ ... gₙ₋₁ d₀ ... dₙ₋₁,
    Split(s) = [g₀, ..., gₙ₋₁] ∧
    l = [d₀, ..., dₙ₋₁] ∧
    ∀ i ∈ [0, n),
      IsBalanced(gᵢ) ∧
      MaxNestingDepth(gᵢ, dᵢ)

## 7

![image-20250725112232686](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725112232686.png)

∀str, In(str, output) ↔ (In(str, strings) ∧ Contains(str, s))

## 9

![image-20250725112221212](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725112221212.png)

Spec(input, output) :=

length(output) == length(input) ∧

∀i. 0 ≤ i < length(output) ∧output(i) = m∧
        (∀j. 0 ≤ j ≤ i → input[j] ≤ m) ∧
        (∃j. 0 ≤ j ≤ i ∧ input[j] = m) 



## 10

![image-20250725112209472](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725112209472.png)

Spec(input, output) :=

prefix(input, output) ∧
palindrome(output) ∧
∀ p, 
  (prefix(input, p) ∧ palindrome(p)) → length(output) ≤ length(p))



## 11

![image-20250725112147997](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725112147997.png)

Spec(a, b, output) :=
length(output) == length(a) ∧
∀ i ∈ [0, length(output)),
  a[i] = b[i] -> output[i] = '0' /\
  a[i]<>b[i] -> output[i] = '1'



## 12

![image-20250725110628645](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725110628645.png)

Spec(input, output) :=
(length(input) = 0 ∧ output = {}) ∨
(length(input) > 0 ∧
  ∃ i ∈ [0, length(input)),
    output = input[i] ∧
	(* 所有元素长度 ≤ output *)
    ∀ j ∈ [0, length(input)), length(input[j]) ≤ length(output) ∧   
	( 在 i 之前的元素严格短于 output *)
    ∀ j ∈ [0, i), length(input[j]) < length(output)

)



## 13

![image-20250725112459144](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725112459144.png)

Spec(a, b, output) :=

(a mod output = 0) ∧
(b mod output = 0) ∧
(∀ x ∈ ℕ, (a mod x = 0 ∧ b mod x = 0) → x ≤ output)



## 14

![image-20250725112926991](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725112926991.png)

Spec(input, output) :=

(length(input) = 0 ∧ output = {}) ∨
(length(input) > 0 ∧
  length(output) = length(input) ∧
  ∀ i ∈ [0, length(input)),
    length(output[i]) = i ∧
    prefix(output[i], input)
)



## 15

![image-20250725134640074](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725134640074.png)





## 16

![image-20250725140134445](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725140134445.png)

Spec(s, k) :=
∃ D : set(Char),
  (* 1. 每个 s(i) 的小写形式都在 D 中 *)
  (∀ i ∈ [0, length(s)), ∃ d ∈ D, d = lower(s[i])) ∧

  (* 2. D 中的每个字符都能由某个 s(i) 得到 *)
  (∀ d ∈ D, ∃ i ∈ [0, length(s)), d = lower(s[i])) ∧

  (* 3. D 中字符互异 *)
  (∀ d1 ∈ D, ∀ d2 ∈ D, d1 ≠ d2 ∧ lower(d1) ≠ lower(d2)) ∧

  (* 4. 输出等于集合大小 *)
  k = |D|



## 17

![image-20250725145008115](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250725145008115.png)

Spec(s, beats) := 
∃ tokens : list(string),
  split_by_space(s, tokens) ∧                   (* s 按空格分割 等于 tokens )
(∀ i ∈ [0, length(tokens)),                          ( 对每个 token *)
	tokens[i] = "o" \/
    tokens[i] = "o|" \/
    tokens[i] = ".|" ）

(∀ i ∈ [0, length(tokens)),                          (* 对每个 token *)
	tokens[i] = "o" → beats[i] = 4 ∧
    tokens[i] = "o|" → beats[i] = 2 ∧
    tokens[i] = ".|" → beats[i] = 1）

  ∧
  length(beats) = length(tokens)                              (* 输出长度等于 token 数 *)



## 18

![image-20250726175809334](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250726175809334.png)

表示从 `input` 的第 `i` 位开始，与 `substr` 完全匹配

match_at(i, input, substr) :=
  length(substr) > 0 ∧
  i + length(substr) ≤ length(input) ∧
  ∀ j ∈ [0, length(substr)), input[i + j] = substr[j]



Spec(input, substring, output) :=

​	(∃ index : list(nat),

​		∀ i ∈ [0, length(input)-length(substr)], match_at(i, input, substr) → i ∈ index ) ∧

​    (∀ i ∈ index, match_at(i, input, substr)) ∧

​	output = length(index)



## 19

![image-20250726183458381](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250726183458381.png)

IsPermutation(l1, l2) ≡
  ∀ l ∈ l1, ∃ l' ∈ l2, l = l' ∧

 ∀ l ∈ l2, ∃ l' ∈ l1, l = l'

IsSorted(l) ≡
  ∀ i j. (0 ≤ i < j < len(l)) →
    ∃ n_i n_j. WordToNum(l[i], n_i) ∧ WordToNum(l[j], n_j) ∧ n_i ≤ n_j

Spec(input, output) :=

∃ input_list, output_list,
    split_by_space(input, input_list) ∧
    split_by_space(output, output_list) ∧
    IsPermutation(input_list, output_list) ∧
    IsSorted(output_list)



## 20

![image-20250726191719354](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250726191719354.png)

Spec(input : list float, output1 : float, output2 : float) :=

​	output1 ∈ input /\ output2 ∈ input
​	(∀ i, j ∈ [0, length(input)), i <> j →
​		 abs(output1 - output2)  ≤  abs(input[i] - input[j] )) ∧
​	ouput1 ≤ output2



## 21

![image-20250726192430214](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250726192430214.png)

Spec(input : list float, output : list float) :=

​	length(input) = length(output) ∧
​	min(input) <> max(input)  ->	∀ i ∈ [0, length(input)), output[i] = (input[i] - min(input)) / (max(input) - min(input))  /\
​	**min(input) == max(input)**  ->     ∀ i ∈ [0, length(input)), output[i] =0



## 22

![image-20250727004533737](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727004533737.png)

Spec(input : list, output : list int) :=

​	∀ i ∈ output, IsInteger(i) ∧
​	(∀ i ∈ input, IsInteger(i) → i ∈ output) ∧
​	∀ i ∈ output, i ∈ input
​	∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l



## 23

![image-20250727005325924](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727005325924.png)

​	Spec(input : string, output : int) :=

​		output = length(input)



## 24

![image-20250727005416776](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727005416776.png)

Spec(input : int, output : int) :=

​	input % output = 0 ∧

​	∀i ∈ [1, input], input % i = 0 → i  ≤  output 



## 25

![image-20250727144555012](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727144555012.png)

Spec(input : int, output : list int) :=

​	IsSorted(output) ∧

​	Multiply(output) = input ∧

​	∀i ∈ output, IsPrime(i)



## 26

![image-20250727145810281](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727145810281.png)

Spec(input : list int, output : list int) :=

(∀j ∈ [0, length(output)),
  ∃i ∈ [0, length(input)),
    input(i) = output(j)
    ∧ ∀k ∈ [0, length(input)), input(k) = input(i) → (k = i) )      ∧ -- output中每个元素都在input里面，且在input 中只出现过一次

 (∀i ∈ [0, length(input)):
      (∀k ∈ [0, length(input) ), input(k) = input(i) → (k = i)) →        -- input(i) 只出现一次
        ∃j ∈ [0, m), output(j) = input(i) ）∧                  -- 就一定出现在 output 中

（∀j1, j2 ∈ [0, length(output)), ∃i1, i2 ∈ [0, length(input)):
      output(j1) = input(i1) ∧ output(j2) = input(i2)  ∧ j1 < j2 → i1 < i2）     -- 保持顺序



## 27

![image-20250727151547372](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727151547372.png)

Spec(input : string, output : string) :=

​	length(input) = length(output) ∧
​	∀i ∈ [0, length(input)),  IsLow(input[i]) → output[i] = Upper(input[i]) ∧ IsUp(input[i]) → output[i] = Lower(input[i]) /\
​	∀i ∈ [0, length(input)), ~IsLow(input[i]) /\\ ~IsUp(input[i]) -> output[i] = input[i]



## 28

![image-20250727152554067](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727152554067.png)

Spec(input : list string, output : string) :=

​	Concat(input, output)



## 29

![image-20250727180118462](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727180118462.png)

Spec(input : list string, substring : string, output list string) :=

​	∀s ∈ output, s  ∈ input /\
​	∀s ∈ output, prefix(substring, s) /\
​	∀s ∈ input, prefix(substring, s) → s ∈ output /\
​	∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l



## 30

![image-20250727180528688](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727180528688.png)

Spec(input : list float, output : list float) :=

​		∀f ∈ output, f > 0 /\
​		∀f ∈ output, f ∈ intput /\
​		∀f ∈ input, f > 0 → f ∈ output
​		∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l



## 31

![image-20250727181919452](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727181919452.png)

Spec(input : int, output : bool) :=

​	output = prime(input)



## 32

![image-20250727185857170](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727185857170.png)



Spec(input : list float, output : float) :=

​	$∑_{i=0}^{n}$ input[i] * output^i = 0



## 33

![image-20250727191931102](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727191931102.png)

Spec(input : list int, output : list int) :=

​	length(input) = length(output) /\
​	∀i ∈ [0, length(input)), i % 3 <> 0 → output[i] = input[i]  /\
​	∀i ∈ [0, length(output)), ∃  j ∈ [0, length(intput))  i %3 = 0 -> j % 3 = 0 /\ input[j] = output[i] 
​	∀i ∈ [0, length(input)), ∃  j ∈ [0, length(output))  i %3 = 0 -> j % 3 = 0 /\ output[j] = input[i] /\ 
​	∀i,j ∈ [0, length(input)), i,j % 3 == 0 /\ i < j → output[i] ≤ output[j]



## 34

![image-20250727214151135](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727214151135.png)

Spec(input : list int, output : list int) :=
	IsSorted(output) /\
	IsUnique(output) /\
	∀i ∈ output <-> i ∈ input



## 35

![image-20250727214450624](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727214450624.png)

Spec(input : list int, output : int) :=
	output = max(input)

## 36

![image-20250727214541289](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727214541289.png)

OccursDigit(x, d, t) ↔ ∃s (ToDigitList(x, s) ∧ CountDigit(s, d, t))
Num7sIn(x) = t  ↔  OccursDigit(x, 7, t)

Spec(input : int, output : int) :=
  outout = $∑_{x=0}^{input-1}$ (if DivBy11Or13(x) then Num7sIn(x) else 0)



## 37

![image-20250727221453612](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727221453612.png)

Spec(input : list int, output : list int) :=

​	length(input) = length(output) /\
​	∀i ∈ [0, length(input)), i % 2 <> 0 → output[i] = input[i]  /\
​	∀i ∈ [0, length(output)), ∃  j ∈ [0, length(intput))  i %2 = 0 -> j % 2 = 0 /\ input[j] = output[i] 
​	∀i ∈ [0, length(input)), ∃  j ∈ [0, length(output))  i %2 = 0 -> j % 2 = 0 /\ output[j] = input[i] /\ 
​	∀i,j ∈ [0, length(input)), i,j % 2 == 0 /\ i < j → output[i] ≤ output[j]



## 38

![image-20250727222849553](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727222849553.png)

Spec(input ：string, output : string) :=

​	∃n， n = (length(input) / 3) *3 -1  /\
​		(∀i ∈ [0, length(input)),   i+1 % 3 = 0  → i ≤ n) /\
​		(∀i ∈ [0, n], i+1 % 3 = 2 → output[i] = input[i-1] /\ 
​							  i+1 % 3 = 1 → output[i] = input[i+2] /\ 
​							  i+1 % 3 =0 → output[i] = input[i-1]) /\
​		(∀i ∈ (n, length(input)), output[i] = input[i])



## 39

![image-20250727231715035](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250727231715035.png)

Spec(input : n. output : n) :=

​	 IsPrimeFib(r) ∧ |{y ∈ ℕ | y < r ∧ IsPrimeFib(y)}| = n - 1



## 40

![image-20250728001019410](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728001019410.png)

Spec(input : list int, output : bool) :=

​	∃i,j,k i<>k /\ i<>j /\ j<>k /\ input[i] + input[j] + input[k] = 0 → output = true /\
​	∀i,j,k i<>k /\ i<>j /\ j<>k /\ input[i] + input[j] + input[k] <> 0 → output = false



## 41

![image-20250728001557924](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728001557924.png)

Spec(input : int, output : int) :=

​	output = input * input



## 42

![image-20250728001836594](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728001836594.png)

Spec(input : list int, output : list int) :=

​	length(input) = length(output) /\
​	∀i ∈ [0, length(input)), outpu[i] = input[i] + 1



## 43

![image-20250728002036065](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728002036065.png)

Spec(input : list int, output : bool) :=

​	∃i,j i<>j  /\ input[i] + input[j]  = 0 → output = true /\
​	∀i,j i<>j  /\ input[i] + input[j]  <> 0 → output = false



## 44

![image-20250728002242380](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728002242380.png)

Spec(x : int, base : int, output : string) :=

​	∀i ∈ [0, length(output)), output[i] < base /\
​	$∑_{i=0}^{length(output)-1}$ ToNum(output[i]) * base^i = x



## 45

![image-20250728004151305](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728004151305.png)

Spec(side : float, high : float, output : float) :=
	output = side * high / 2



## 46

![image-20250728004338479](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728004338479.png)

Spec(input : int, output : int) :=

​	∃ Fib : list int,
​		Fib[0] = 0 /\ Fib[1] = 0 /\ Fib[2] = 2 /\ Fib[3] = 0 /\
​		∀i ∈ N, i >3 → Fib[i] = Fib[i-1] + Fib[i-2] + Fib[i-3] + Fib[i-4] /\
​		output = Fib[input]



## 47

![image-20250728004914336](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728004914336.png)

Spec(input : list float, output : float) :=

​	∃Sorted_input, 
​		Sorted(input, Sorted_input) /\
​		length(input) % 2 =1  → output = Sorted_input[length(input) / 2] /\
​		length(input) % 2 <>1  → output = (Sorted_input[length(input) / 2] + Sorted_input[length(input) / 2 -1]) /2



## 48

![image-20250728005552335](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728005552335.png)

Spec(input : string, output : bool) :=
 output = true ↔ ∀i ∈ [0, length(input) / 2), input[i] = input[length(input) - 1 - i]



## 49

![image-20250728010443410](C:\Users\86158\AppData\Roaming\Typora\typora-user-images\image-20250728010443410.png)

Spec(n : int, p : int, output : int) :=

​	output = 2^n % p 

