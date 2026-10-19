# teichlab — 同構即相同（isomorphism is identity）

用 [MoonBit](https://www.moonbitlang.com/) 實作的九個數學結構，**全部通過機械驗證**：
泰希米勒空間、序、路徑空間、格、尼雲維奇拓撲、規範形式、導範疇、範疇化、熱帶化。

核心主張：**同構即相同**。每個結構都給出一個規範形（canonical form），
使得「兩個物件同構」退化成「兩個規範形相等」——於是不必在執行期比較物件，
只需比較已經算好的資料。所有的認證與引理都在**編譯期**完成，
承載型別是無盒（unboxed）單欄位結構，release build 下摺疊成一條 `mov`：零成本抽象。

```
moon test          # 70 passed, 0 failed
moon run cmd/main  # 十一個套件各印出一條由演算法算出來的結論
```

## 安裝工具鏈

```bash
curl -sSL https://cli.moonbitlang.com/install/unix.sh | bash   # 裝到 ~/.moon
export PATH="$HOME/.moon/bin:$PATH"
moon version       # 本專案以 0.1.20261016 (1af328f 2026-10-16) 驗證
```

## 套件一覽

| 套件 | 內容 | 測試 |
|---|---|---|
| `src/tl` | 型別層自然數、幽靈型別憑證、`Iso`（零成本抽象的地基） | 7 |
| `src/nf` | Smith / Hermite 標準形、Gröbner 基、初始理想 | 9 |
| `src/order` | 偏序、Birkhoff 表示、Dedekind–MacNeille、鉤長公式 | 7 |
| `src/path` | 路徑空間、長度索引路徑、自由群胚正規形、π₁、路代數 | 6 |
| `src/lat` | LLL 歸約、Hermite 分類、Hadamard 界 | 4 |
| `src/teich` | Fricke、Markoff、McShane、Fenchel–Nielsen | 7 |
| `src/valued` | p 進賦值、Hensel 引理、Newton 多邊形、估值環 | 7 |
| `src/trop` | 熱帶半環、Kapranov 定理、熱帶矩陣、熱帶 Grassmannian | 7 |
| `src/derived` | 鏈複形、同調、映射錐、Künneth、Ext / Tor、泛係數定理 | 5 |
| `src/cat` | FinSet 範疇化、分次向量空間與 Gauss 二項式、K₀ | 6 |
| `src/nis` | 尼雲維奇拓撲：平展 / 完全分解、基變換、截面、下降 | 5 |

## 七個「規範形」

| 結構 | 同構的對象 | 規範形 |
|---|---|---|
| 有限生成阿貝爾群 | SNF | 不變因子 |
| ℤᵐ 的子格 | HNF | Hermite 標準形 |
| 多項式對理想的餘式 | 標準單項式 | Gröbner 基下的正規形 |
| 自由群元素 | 詞約簡 | 約簡詞（合流 ⇒ 唯一） |
| 分次向量空間 | Hilbert 級數 | 各次維數陣列 |
| Dᵇ(ℤ) 的複形 | 同調 | ⊕ₙ Hₙ[n]（SNF 給出具體擬同構） |
| Teichmüller 空間的點 | Fricke 座標 | (x,y,z) 滿足 Markoff 三次式 |

完整的定義、定理與公式見 **[THEOREMS.md](THEOREMS.md)**。

## 工程狀態

| 項目 | 狀態 |
|---|---|
| `moon test` | 70 passed / 0 failed |
| `moon clean && moon check` 警告數 | 0 |
| 未被任何程式引用的公開 API | 0 |
| 跨套件重複實作 | 0（`ipow` / `gcd` / 矩陣乘法 / 絕對值各只有一份） |

幽靈型別參數（`NatV[A]`、`Vec[N,A]`、`Edge[A,B]`…）刻意觸發的
`unused_type_variable` 警告已在 `src/tl/moon.pkg` 與 `src/path/moon.pkg`
以 `warnings = "-unused_type_variable"` 明確豁免並註明理由。

## 授權

Apache-2.0
