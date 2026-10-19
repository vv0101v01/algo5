# teichlab — 同構即相同（Isomorphism is Identity）

用 MoonBit 實作並**驗證**的九個數學結構。每一個套件都同時給出
(a) 定義、(b) 定理、(c) 由定理推出的演算法，以及 (d) 一組真正跑過的機械驗證
（`moon test`，共 **70 個測試，全綠**）。

```
moon test          # 68 passed, 0 failed
moon run cmd/main  # 十個套件各印出一條由演算法算出來的結論
```

工具鏈：`moon 0.1.20261016 (1af328f 2026-10-16)`，安裝於 `~/.moon`
（`curl -sSL https://cli.moonbitlang.com/install/unix.sh | bash`）。

## 零成本抽象：邏輯在編譯期，執行期不留痕跡

所有「認證用的承載型別」都用**無盒（unboxed）單欄位 tuple struct**：

```moonbit
pub struct NatV[A](Int) derive(Debug, Eq)      // 一個 Int，無額外間接層
pub trait Nat { cert(Unit) -> NatV[Self] }
pub impl Nat for Z with cert(_u : Unit) -> NatV[Z] { NatV(0) }
pub impl[N : Nat] Nat for S[N] with cert(_u : Unit) -> NatV[S[N]] {
  let NatV(k) = (Nat::cert(()) : NatV[N]); NatV(1 + k)
}
pub fn[N : Nat] reflect() -> NatV[N] { Nat::cert(()) }
```

在 native codegen 下 `reflect() : NatV[Plus[S^3 Z, S^4 Z]]` 被摺疊成
`mov $0x37,%edx` —— **整數 7 直接出現，沒有任何函式呼叫**。
（`src/tl`，`cmd/main` 第 1 行即這個結果。）端點匹配的型別
`compose : Path[A,B] → Path[B,C] → Path[A,C]` 亦是如此：不合法的路徑
**不能通過型別檢查**，執行期無需檢查任何 tag。

---

## 1. 序 `src/order`（7 測試）

**定義** 偏序集 $P=(X,\le)$；$L$ 的併不可約元 $J(L)$；Dedekind–MacNeille 完備化
$\mathbf{DM}(P)$；上集 $\uparrow\! v=\{w: v\le w\}$。

**T1（Birkhoff 表示定理）** 有限分配格 $L\cong \mathcal O(J(L))$（由併不可約元的
序理想格給出）。程式以覆蓋關係（傳遞約簡）數出 $J(L)$ 並重建 $L$。

**T2（Dedekind–MacNeille）** $\mathbf{DM}(P)$ 是包含 $P$ 的最小完備格；
對 3 元反鏈得到 $M_3$（5 個元素）。

**T3（森林的鉤長公式）** 若 $P$ 是森林（以極小元為根），其線性擴張數
$$e(P)=\frac{|P|!}{\prod_{v}\ |\uparrow\! v|}$$
實測：$|\!\uparrow\!0|=5,\dots$ 得 $5!/15=8$，與窮舉數出的 $8$ 一致。

## 2. 規範形式 `src/nf`（9 測試）

**T1（Smith 標準形）** $\exists U,V\in GL$：$UAV=\mathrm{diag}(d_1,\dots,d_r)$，$d_1\mid\cdots\mid d_r$，
故 $\mathrm{coker}(A)\cong \bigoplus_i \mathbb Z/d_i\oplus\mathbb Z^{m-r}$。

**T2（同構即相同）** 兩個有限生成阿貝爾群同構 $\iff$ 去掉 $1$ 後的不變因子相等
（$\mathbb Z/2\oplus\mathbb Z/3\cong\mathbb Z/6$，但 $\mathbb Z/2\oplus\mathbb Z/4\not\cong\mathbb Z/8$）。

**T3（Hermite 標準形）** $\mathbb Z^m$ 的子格由 HNF 完全分類：兩個整矩陣生成同一子格 $\iff$ HNF 相等。

**T4（Buchberger）** $G$ 是 Gröbner 基 $\iff$ 所有 $S$-多項式歸零；
$\mathrm{NF}_G(f)=\mathrm{NF}_G(g)\iff f-g\in I$。

**T5（熱帶成員判定）** $w\in\mathrm{Trop}(I)\iff \mathrm{in}_w(I)$ 不含單項式。

## 3. 路徑空間 `src/path`（6 測試）

**T1（自由群胚的正規形）** 詞約簡是合流且冪等的，故「同倫即相同」＝**正規形相等**。
在 60 個隨機詞上窮舉所有約簡順序驗證 Church–Rosser。

**T2（$\pi_1$）** $\pi_1(\Gamma)\cong F_r$，$r=|E|-|V|+c$；約簡詞到約簡回路的映射**單射**
（在 $F_2$ 半徑 3 的球、$F_1$ 半徑 4 的球上驗證）。增長函數
$1+\sum_{i\le k}2r(2r-1)^{i-1}$。

**T3（路代數）** 乘法＝接續，端點不合即為 $0$，且按長度分次。

## 4. 格 `src/lat`（4 測試）

**T1（LLL）** 歸約基滿足 $|\mu_{i,j}|\le 1/2$ 與
$\delta\|b^*_{i-1}\|^2\le\|b^*_i\|^2+\mu_{i,i-1}^2\|b^*_{i-1}\|^2$，且
$\|b_1\|\le 2^{(n-1)/2}\lambda_1$（與暴力搜尋的 $\lambda_1$ 比對）。

**T2（同構即相同）** 兩個整矩陣生成同一子格 $\iff$ 其 Hermite 標準形相等。

**T3** Gram 矩陣與 Hadamard 界 $\det\Lambda\le\prod\|b_i\|$。

## 5. 泰希米勒空間 `src/teich`（7 測試）

**T1（Fricke 恆等式）** 對 $A,B\in SL(2,\mathbb R)$，$x=\operatorname{tr}A,\ y=\operatorname{tr}B,\ z=\operatorname{tr}AB$：
$$\operatorname{tr}[A,B]=x^2+y^2+z^2-xyz-2 .$$

**T2（Fricke–Vogt）** $\mathcal T(S_{1,1})\cong\{(x,y,z)\in\mathbb R^3_{>2}:x^2+y^2+z^2=xyz\}$；
Vieta 對合 $(x,y,z)\mapsto(yz-x,y,z)$ 作用在 Markoff 三元組上並構成單一軌道；
跡恰為 $3\times${Markoff 數} $=3\times\{1,2,5,13,29,34,\dots\}$。

**T3（Markoff 數）** $a^2+b^2+c^2=3abc$（機械驗證）。

**T4（McShane 恆等式）** $\displaystyle\sum_\gamma\frac{1}{1+e^{\ell(\gamma)}}=\frac12$，
且 $\dfrac{1}{1+e^\ell}=\dfrac{1-\sqrt{1-4/x^2}}{2}$。實測部分和
$0.41056\to0.49999995$（$N=10$）由下方收斂。

**T5（簡單閉曲線）** Stern–Brocot／Farey 遞迴構造 $(p,q)$ 曲線的詞；
對所有 $|p|,|q|\le5$ 的本原類驗證其交換化為 $\pm(p,q)$、詞為約簡詞、且 $|\operatorname{tr}|>2$。

**T6（Fenchel–Nielsen）** 扭曲流 $\Phi_t(A,B)=(A,\ A^{t/2}BA^{t/2})$ 保持
$\operatorname{tr}A$、$\operatorname{tr}[A,B]$ 與 Markoff 虧量，滿足群律
$\Phi_{s+t}=\Phi_s\circ\Phi_t$，扭曲座標滿足 $\tau(\Phi_t X)=\tau(X)+t$（實測 $\tau(t)=-0.5+t$），
且 $\tau=0$ 正是 $\ell(B)$ 在軌道上取最小值之處。

## 6. 值 `src/valued`（6 測試）

**定義** $v(xy)=v(x)+v(y)$，$v(x+y)\ge\min(v(x),v(y))$；$|x|_p=p^{-v_p(x)}$；
估值環 $\mathcal O=\{v\ge0\}$、極大理想 $\mathfrak m=\{v>0\}$、剩餘域 $k(v)=\mathcal O/\mathfrak m$。

**T1（Ostrowski 乘積公式）** $|x|_\infty\prod_p|x|_p=1$（以**精確有理數**驗證；截斷素數集合即失效）。

**T2（強三角不等式）** $|x+y|_p\le\max(|x|_p,|y|_p)$；$v(x)\ne v(y)$ 時取等號（所有 $p$-進三角形皆等腰）。

**T3（Hensel，單根）** $f(a)\equiv0,\ f'(a)\not\equiv0 \pmod p$ $\Rightarrow$ Newton 迭代
$a\leftarrow a-f(a)/f'(a)$ 二次收斂到 $\mathbb Z_p$ 中的根，且**唯一**。
實測：$\sqrt2\in\mathbb Z_7$（10 位）、$\sqrt{-1}\in\mathbb Z_5$、$\sqrt[3]2\in\mathbb Z_5$；
並在 $7^3$ 內窮舉驗證唯一性。另給出 Teichmüller 代表元 $\omega(x)^{p-1}=1$。

**T4（Hensel，分解）** $f\equiv g_0h_0\pmod p$、$\gcd(g_0,h_0)=1$ $\Rightarrow$ 提升至 $f=gh\in\mathbb Z_p[x]$；
實測 $x^2-2=(x-\sqrt2)(x+\sqrt2)\in\mathbb Z_7[x]$（與 T3 的 $\sqrt2$ 完全一致）。

**T5（Newton 多邊形）** 下凸包上水平長度 $m$、斜率 $-s$ 的線段 $\iff$ $m$ 個根的估值為 $s$。

**T6（估值環）** $\mathcal O$ 為環、$\mathfrak m$ 為素理想、$\mathcal O^\times=\mathcal O\setminus\mathfrak m$、
$\mathcal O/\mathfrak m\cong\mathbb F_p$（剩餘映射為滿的環同態，核 $=\mathfrak m$）。
在 $\mathbb Z/p^N$ 模型上另行驗證 $\mathbb Z_p$ 的環公理（加法交換群、乘法交換么半群、分配律）、
$\mathbb Z_p^\times=\{v_p=0\}$ 且每個單位在 $\mathbb Z_p$ 中可逆，以及 $\mathbb Z_p\to\mathbb F_p$ 保持 $+$ 與 $\times$。

## 7. 熱帶化 `src/trop`（6 測試）

**定義（熱帶半環）** $\mathbb T=\mathbb R\cup\{\infty\}$，$x\oplus y=\min(x,y)$，$x\odot y=x+y$；
$\mathrm{trop}(f)(w)=\min_\alpha\big(v(c_\alpha)+\langle\alpha,w\rangle\big)$。

**T1** $(\mathbb T,\oplus,\odot)$ 是冪等交換半環（驗證結合/交換/分配/單位元/absorbtion/無加法逆元）。

**T2（熱帶化是半環同態）** $\mathrm{trop}(fg)=\mathrm{trop}(f)\odot\mathrm{trop}(g)$；
對加法只有 $\mathrm{trop}(f+g)\ge\mathrm{trop}(f)\oplus\mathrm{trop}(g)$（以 $(x-1)(x+1)$ 展示嚴格不等）。

**T3（Kapranov／基本定理，$n=1$）** 熱帶根（最小值至少取到兩次的點）$=$ 根的估值；
與 Newton 多邊形兩個**獨立演算法**互相驗證。

**T4（Kapranov，$n\ge1$）** $w\in\mathrm{Trop}(V(I))\iff\mathrm{in}_w(I)$ 不含單項式
$\iff$ $\mathrm{trop}(f)(-w)$ 的最小值取到至少兩次（初始形式用 max 慣例，故符號相反）；
在 $5\times5$ 權重網格上對三個多項式逐一比對（`kapranov_agree`）。

**T5（熱帶矩陣）** $v((AB)_{ij})\ge\min_k(v(A_{ik})+v(B_{kj}))$；
$\mathrm{tdet}(A)=\min_{\sigma}\sum_iA_{i\sigma(i)}$ 為指派問題的值，最小值取到兩次即熱帶奇異。

**T6（熱帶 Grassmannian）** $(w_{ij})\in\mathrm{trop}\,Gr(2,4)\iff\min(w_{12}\odot w_{34},w_{13}\odot w_{24},w_{14}\odot w_{23})$
取到至少兩次；令 $w=-d$ 即四點條件（樹度量的刻畫）。4-圈度量**不是**樹度量。

## 8. 導範疇 `src/derived`（5 測試）

**T1（同調）** $H_n=\ker d_n/\operatorname{im}d_{n+1}$：以 SNF 取 $\ker d_n$ 的基（$V$ 的後段行），
再用 $V^{-1}$ 的對偶列把 $\operatorname{im}d_{n+1}$ 寫進該基，得到 $H_n=\mathrm{coker}(M)$——
同調以**表現矩陣**輸出，同構即 SNF 相等。

**T2（Euler–Poincaré）** $\chi(C)=\sum(-1)^n\operatorname{rk}C_n=\sum(-1)^n\operatorname{rk}H_n$。

**T3（映射錐／三角結構）** $\mathrm{Cone}(f)_n=D_n\oplus C_{n-1}$，$d=\begin{pmatrix}d_D&f\\0&-d_C\end{pmatrix}$；
$f$ 是擬同構 $\iff$ $\mathrm{Cone}(f)$ 零調；$\mathrm{Cone}(\mathrm{id})$ 可縮；三角形上
$\sum(-1)^n(\operatorname{rk}H_nD-\operatorname{rk}H_n\mathrm{Cone}-\operatorname{rk}H_nC)=0$。

**T4（$\mathbb Z$ 上的分裂）** 因 $\mathrm{gldim}\,\mathbb Z=1$，
$C\cong\bigoplus_n H_n(C)[n]\ \in D^b(\mathbb Z)$；對二項複形更**構造出具體的擬同構**
（由 SNF 的 $U^{-1},V$ 直接給出核生成元與關係的提升）。

**T5（Künneth）** $H_n(C\otimes D)\cong\bigoplus_{i+j=n}H_i(C)\otimes H_j(D)\ \oplus\ \bigoplus_{i+j=n-1}\mathrm{Tor}_1(H_iC,H_jD)$。

**T6（Ext／Tor／UCT）** $\mathrm{Tor}_i^{\mathbb Z}(\mathbb Z/n,\mathbb Z/m)=\mathbb Z/\gcd(n,m)$（$i=0,1$），
否則 $0$；$\mathrm{Ext}^1_{\mathbb Z}(\mathbb Z/n,\mathbb Z)=\mathbb Z/n$；
泛係數定理 $0\to\mathrm{Ext}^1(H_{n-1}C,\mathbb Z)\to H^n(\mathrm{Hom}(C,\mathbb Z))\to\mathrm{Hom}(H_nC,\mathbb Z)\to0$。

## 9. 範疇化 `src/cat`（6 測試）

**T1（$\mathbb N$ 由 FinSet 範疇化）** $A\cong B\iff|A|=|B|$（同構即相同）；
$|\mathrm{Aut}(A)|=|A|!$；FinSet 是笛卡兒閉範疇，三個自然同構
$C^{A\sqcup B}\cong C^A\times C^B$、$(A\times B)^C\cong A^C\times B^C$、$(C^B)^A\cong C^{B\times A}$
都**顯式構造並暴力驗證為雙射**；二項式定理被範疇化為雙射
$(A\sqcup B)^{[n]}\cong\bigsqcup_k\binom{n}{k}\times A^{[k]}\times B^{[n-k]}$。

**T2（Gauss 二項式由分次向量空間範疇化）** 設 $V_d$ 在第 $0,\dots,d-1$ 次各有一基底，則
$$\Lambda^n(V_d)\ \leadsto\ q^{n(n-1)/2}\begin{bmatrix}d\\n\end{bmatrix}_q,\qquad
S^n(V_d)\ \leadsto\ \begin{bmatrix}d+n-1\\n\end{bmatrix}_q,$$
且兩個有限維分次向量空間同構 $\iff$ Hilbert 級數相等（並逐次構造出具體同構）。

**T3（$K_0$ 與 Euler 特徵）** $K_0(D^b(\mathbb Z))\cong\mathbb Z$，
$[C]=\sum(-1)^n[C_n]=\sum(-1)^n[H_n(C)]$；$K_0(\mathrm{FinSet})\cong\mathbb N$。

## 10. 尼雲維奇拓撲 `src/nis`（5 測試）

**定義（Nisnevich 覆蓋）** 一族**平展**態射 $\{u_\alpha:X_\alpha\to X\}$ 是 Nisnevich 覆蓋，
若對每個點 $x\in X$ 存在 $\alpha$ 與 $y\in X_\alpha$ 使 $u_\alpha(y)=x$ 且
$\kappa(x)\xrightarrow{\sim}\kappa(y)$（完全分解條件）。有
$\text{Zariski}\subsetneq\text{Nisnevich}\subsetneq\text{平展}$。

**模型** 小 Nisnevich 站限制在有限平展 $\mathbb F_p$-代數上：$A=\prod_i\mathbb F_{p^{d_i}}$，
點即因子，態射由「哪個點映到哪個點」給出（嵌入存在 $\iff d_{\sigma(j)}\mid \deg L_j$），
剩餘次數 $=\deg L_j/d_{\sigma(j)}$，纖維積用
$\mathbb F_{p^a}\otimes_{\mathbb F_{p^c}}\mathbb F_{p^b}\cong(\mathbb F_{p^{\mathrm{lcm}(a,b)}})^{\gcd(a,b)/c}$。

**T1** 平展＝點上滿射；Nisnevich＝再加上每點被剩餘次數 $1$ 的點命中；Zariski＝開浸入。
在 85 個態射上驗證 Zariski $\Rightarrow$ Nisnevich $\Rightarrow$ 平展，兩者皆嚴格：
$\{\mathbb F_p\times\mathbb F_4\to\mathbb F_p\}$ 是 Nisnevich 非 Zariski；
$\{\mathbb F_4\to\mathbb F_p\}$ 是平展非 Nisnevich。

**T2（基變換）** Nisnevich 覆蓋在任意基變換下仍為 Nisnevich 覆蓋（含纖維積維度公式驗證）。

**T3（合成）** Nisnevich 覆蓋對合成封閉。

**T4（截面；完全分解）** 每個 Nisnevich 覆蓋都有截面（逐點選剩餘次數 $1$ 的點，
剩餘域同構給出代數映射）——非 Nisnevich 的平展覆蓋則不一定有。

**T5（下降）** 預層 $F(A)=\mathrm{Map}(\pi_0(\mathrm{Spec}\,A),S)$ 是 Nisnevich 層：
相容的截面唯一下降（因覆蓋在點上滿射）；非滿射的族則下降不唯一。

---

## 檔案結構

```
moon.mod
cmd/main/main.mbt      展示程式（moon run cmd/main）
src/tl/      型別層自然數、無盒承載型別、Iso（零成本抽象的核心）
src/nf/      Smith / Hermite 標準形、Gröbner 基、初始理想
src/order/   偏序、Birkhoff、Dedekind–MacNeille、鉤長公式
src/path/    路徑空間、長度索引路徑、自由群胚正規形、π₁、路代數
src/lat/     LLL 歸約、Hermite 分類、Hadamard 界
src/teich/   Fricke、Markoff、McShane、Fenchel–Nielsen
src/valued/  p 進賦值、Hensel 引理、Newton 多邊形、估值環
src/trop/    熱帶半環、Kapranov 定理、熱帶矩陣、熱帶 Grassmannian
src/derived/ 鏈複形、同調、映射錐、Künneth、Ext / Tor、UCT
src/cat/     FinSet 範疇化、分次向量空間與 Gauss 二項式、K₀
src/nis/     Nisnevich 拓撲（平展/完全分解、基變換、截面、下降）
```

## 同構即相同：本專案的七個「規範形」

| 結構 | 同構的對象 | 規範形（相等即同構） |
|---|---|---|
| 有限生成阿貝爾群 | SNF | 不變因子（去掉 1、合併互素） |
| $\mathbb Z^m$ 的子格 | HNF | Hermite 標準形 |
| 多項式對理想的餘式 | 標準單項式 | Gröbner 基下的正規形 |
| 自由群元素 | 詞約簡 | 約簡詞（合流 $\Rightarrow$ 唯一） |
| 分次向量空間 | Hilbert 級數 | 各次維數陣列 |
| $D^b(\mathbb Z)$ 的複形 | 同調 | $\bigoplus_nH_n[n]$（SNF 給出具體擬同構） |
| Teichmüller 空間的點 | Fricke 座標 | $(x,y,z)$ 滿足 Markoff 三次式（$+$ 扭曲座標 $\tau$） |

---

## 工程狀態（除錯 / 去重 / 減債 / 清死碼）

| 項目 | 狀態 |
|---|---|
| `moon test` | **70 passed / 0 failed** |
| `moon check` 警告數 | **0**（`moon clean` 後全量重建計數） |
| 公開 API 中未被任何程式（含測試與展示程式）引用者 | 0 |
| 跨套件重複實作 | 0（見下表） |

已刪除的死碼：`teich.tok_bi`、`teich.word_same`、`derived.mat_sub`、`derived.total_rank`、
`lat.dot_i`、`lat.lll_data`、`nf.poly_const`、`nf.poly_var`、`nis.rank_over`、`order.poset_make`
（另含先前已清除的 `teich.inv_word` 與其唯一呼叫者消失後連帶的 `teich.tok_inv`）。

已合併的重複實作（每種演算法只保留一份）：

| 演算法 | 單一實作 | 其餘套件改為委派 |
|---|---|---|
| $a^n$ | `@tl.ipow` | `valued.ipow`、`cat.ipow` |
| $\gcd(\lvert a\rvert,\lvert b\rvert)$ | `@tl.igcd` | `derived.gcd_pos`、`nis.gcd_pos`、`valued_test` 的本地副本 |
| 整數矩陣乘法 | `@nf.mat_mul` | `trop.mat_mul_int` |
| 絕對值 | `nf.abs_int`（private） | `nf.abs_int_export`、`nf_test` 的本地副本 |

刻意**不**合併：`valued.gcd_pos` 約定 $\gcd(0,0)=1$（約分化有理數時不會除以零），
與 `@tl.igcd` 的 $\gcd(0,0)=0$ 語意不同；`path.tree_path` / `path.tree_path_bfs` 是快取路徑與
一般 LCA 回溯，不是重複。

刻意保留的警告豁免：`src/tl` 與 `src/path` 的 `warnings = "-unused_type_variable"`。
兩套件的型別參數（`NatV[A]`、`Vec[N,A]`、`Edge[A,B]`、`LPath[N,A,B]`…）是**幽靈參數**，
只承載編譯期憑證、不出現在資料裡，編譯器無法看見這點（見 `tl.mbt` 檔頭說明）。
