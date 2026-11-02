import Covering.Check
import Covering.ScanK.F0
import Covering.ScanK.F1
import Covering.ScanK.F2
import Covering.ScanK.F3
import Covering.ScanK.F4
import Covering.ScanK.F5
import Covering.ScanK.F6
import Covering.ScanK.F7
import Covering.ScanK.F8
import Covering.ScanK.F9
import Covering.ScanK.F10
import Covering.ScanK.F11
import Covering.ScanK.F12
import Covering.ScanK.F13
import Covering.ScanK.F14
import Covering.ScanK.F15
import Covering.ScanK.F16
import Covering.ScanK.F17
import Covering.ScanK.F18
import Covering.ScanK.F19
namespace Covering
open ScanK

/-- Kernel-checked: every odd L ≤ 100000 passes `check`. Assembled from 200 chunk theorems. -/
theorem scan_100000 : scanChunk 0 100000 = true := by
  have h : scanChunk 0 500 = true := c0
  have h : scanChunk 0 1000 = true := scanChunk_append 0 500 500 h c1
  have h : scanChunk 0 1500 = true := scanChunk_append 0 1000 500 h c2
  have h : scanChunk 0 2000 = true := scanChunk_append 0 1500 500 h c3
  have h : scanChunk 0 2500 = true := scanChunk_append 0 2000 500 h c4
  have h : scanChunk 0 3000 = true := scanChunk_append 0 2500 500 h c5
  have h : scanChunk 0 3500 = true := scanChunk_append 0 3000 500 h c6
  have h : scanChunk 0 4000 = true := scanChunk_append 0 3500 500 h c7
  have h : scanChunk 0 4500 = true := scanChunk_append 0 4000 500 h c8
  have h : scanChunk 0 5000 = true := scanChunk_append 0 4500 500 h c9
  have h : scanChunk 0 5500 = true := scanChunk_append 0 5000 500 h c10
  have h : scanChunk 0 6000 = true := scanChunk_append 0 5500 500 h c11
  have h : scanChunk 0 6500 = true := scanChunk_append 0 6000 500 h c12
  have h : scanChunk 0 7000 = true := scanChunk_append 0 6500 500 h c13
  have h : scanChunk 0 7500 = true := scanChunk_append 0 7000 500 h c14
  have h : scanChunk 0 8000 = true := scanChunk_append 0 7500 500 h c15
  have h : scanChunk 0 8500 = true := scanChunk_append 0 8000 500 h c16
  have h : scanChunk 0 9000 = true := scanChunk_append 0 8500 500 h c17
  have h : scanChunk 0 9500 = true := scanChunk_append 0 9000 500 h c18
  have h : scanChunk 0 10000 = true := scanChunk_append 0 9500 500 h c19
  have h : scanChunk 0 10500 = true := scanChunk_append 0 10000 500 h c20
  have h : scanChunk 0 11000 = true := scanChunk_append 0 10500 500 h c21
  have h : scanChunk 0 11500 = true := scanChunk_append 0 11000 500 h c22
  have h : scanChunk 0 12000 = true := scanChunk_append 0 11500 500 h c23
  have h : scanChunk 0 12500 = true := scanChunk_append 0 12000 500 h c24
  have h : scanChunk 0 13000 = true := scanChunk_append 0 12500 500 h c25
  have h : scanChunk 0 13500 = true := scanChunk_append 0 13000 500 h c26
  have h : scanChunk 0 14000 = true := scanChunk_append 0 13500 500 h c27
  have h : scanChunk 0 14500 = true := scanChunk_append 0 14000 500 h c28
  have h : scanChunk 0 15000 = true := scanChunk_append 0 14500 500 h c29
  have h : scanChunk 0 15500 = true := scanChunk_append 0 15000 500 h c30
  have h : scanChunk 0 16000 = true := scanChunk_append 0 15500 500 h c31
  have h : scanChunk 0 16500 = true := scanChunk_append 0 16000 500 h c32
  have h : scanChunk 0 17000 = true := scanChunk_append 0 16500 500 h c33
  have h : scanChunk 0 17500 = true := scanChunk_append 0 17000 500 h c34
  have h : scanChunk 0 18000 = true := scanChunk_append 0 17500 500 h c35
  have h : scanChunk 0 18500 = true := scanChunk_append 0 18000 500 h c36
  have h : scanChunk 0 19000 = true := scanChunk_append 0 18500 500 h c37
  have h : scanChunk 0 19500 = true := scanChunk_append 0 19000 500 h c38
  have h : scanChunk 0 20000 = true := scanChunk_append 0 19500 500 h c39
  have h : scanChunk 0 20500 = true := scanChunk_append 0 20000 500 h c40
  have h : scanChunk 0 21000 = true := scanChunk_append 0 20500 500 h c41
  have h : scanChunk 0 21500 = true := scanChunk_append 0 21000 500 h c42
  have h : scanChunk 0 22000 = true := scanChunk_append 0 21500 500 h c43
  have h : scanChunk 0 22500 = true := scanChunk_append 0 22000 500 h c44
  have h : scanChunk 0 23000 = true := scanChunk_append 0 22500 500 h c45
  have h : scanChunk 0 23500 = true := scanChunk_append 0 23000 500 h c46
  have h : scanChunk 0 24000 = true := scanChunk_append 0 23500 500 h c47
  have h : scanChunk 0 24500 = true := scanChunk_append 0 24000 500 h c48
  have h : scanChunk 0 25000 = true := scanChunk_append 0 24500 500 h c49
  have h : scanChunk 0 25500 = true := scanChunk_append 0 25000 500 h c50
  have h : scanChunk 0 26000 = true := scanChunk_append 0 25500 500 h c51
  have h : scanChunk 0 26500 = true := scanChunk_append 0 26000 500 h c52
  have h : scanChunk 0 27000 = true := scanChunk_append 0 26500 500 h c53
  have h : scanChunk 0 27500 = true := scanChunk_append 0 27000 500 h c54
  have h : scanChunk 0 28000 = true := scanChunk_append 0 27500 500 h c55
  have h : scanChunk 0 28500 = true := scanChunk_append 0 28000 500 h c56
  have h : scanChunk 0 29000 = true := scanChunk_append 0 28500 500 h c57
  have h : scanChunk 0 29500 = true := scanChunk_append 0 29000 500 h c58
  have h : scanChunk 0 30000 = true := scanChunk_append 0 29500 500 h c59
  have h : scanChunk 0 30500 = true := scanChunk_append 0 30000 500 h c60
  have h : scanChunk 0 31000 = true := scanChunk_append 0 30500 500 h c61
  have h : scanChunk 0 31500 = true := scanChunk_append 0 31000 500 h c62
  have h : scanChunk 0 32000 = true := scanChunk_append 0 31500 500 h c63
  have h : scanChunk 0 32500 = true := scanChunk_append 0 32000 500 h c64
  have h : scanChunk 0 33000 = true := scanChunk_append 0 32500 500 h c65
  have h : scanChunk 0 33500 = true := scanChunk_append 0 33000 500 h c66
  have h : scanChunk 0 34000 = true := scanChunk_append 0 33500 500 h c67
  have h : scanChunk 0 34500 = true := scanChunk_append 0 34000 500 h c68
  have h : scanChunk 0 35000 = true := scanChunk_append 0 34500 500 h c69
  have h : scanChunk 0 35500 = true := scanChunk_append 0 35000 500 h c70
  have h : scanChunk 0 36000 = true := scanChunk_append 0 35500 500 h c71
  have h : scanChunk 0 36500 = true := scanChunk_append 0 36000 500 h c72
  have h : scanChunk 0 37000 = true := scanChunk_append 0 36500 500 h c73
  have h : scanChunk 0 37500 = true := scanChunk_append 0 37000 500 h c74
  have h : scanChunk 0 38000 = true := scanChunk_append 0 37500 500 h c75
  have h : scanChunk 0 38500 = true := scanChunk_append 0 38000 500 h c76
  have h : scanChunk 0 39000 = true := scanChunk_append 0 38500 500 h c77
  have h : scanChunk 0 39500 = true := scanChunk_append 0 39000 500 h c78
  have h : scanChunk 0 40000 = true := scanChunk_append 0 39500 500 h c79
  have h : scanChunk 0 40500 = true := scanChunk_append 0 40000 500 h c80
  have h : scanChunk 0 41000 = true := scanChunk_append 0 40500 500 h c81
  have h : scanChunk 0 41500 = true := scanChunk_append 0 41000 500 h c82
  have h : scanChunk 0 42000 = true := scanChunk_append 0 41500 500 h c83
  have h : scanChunk 0 42500 = true := scanChunk_append 0 42000 500 h c84
  have h : scanChunk 0 43000 = true := scanChunk_append 0 42500 500 h c85
  have h : scanChunk 0 43500 = true := scanChunk_append 0 43000 500 h c86
  have h : scanChunk 0 44000 = true := scanChunk_append 0 43500 500 h c87
  have h : scanChunk 0 44500 = true := scanChunk_append 0 44000 500 h c88
  have h : scanChunk 0 45000 = true := scanChunk_append 0 44500 500 h c89
  have h : scanChunk 0 45500 = true := scanChunk_append 0 45000 500 h c90
  have h : scanChunk 0 46000 = true := scanChunk_append 0 45500 500 h c91
  have h : scanChunk 0 46500 = true := scanChunk_append 0 46000 500 h c92
  have h : scanChunk 0 47000 = true := scanChunk_append 0 46500 500 h c93
  have h : scanChunk 0 47500 = true := scanChunk_append 0 47000 500 h c94
  have h : scanChunk 0 48000 = true := scanChunk_append 0 47500 500 h c95
  have h : scanChunk 0 48500 = true := scanChunk_append 0 48000 500 h c96
  have h : scanChunk 0 49000 = true := scanChunk_append 0 48500 500 h c97
  have h : scanChunk 0 49500 = true := scanChunk_append 0 49000 500 h c98
  have h : scanChunk 0 50000 = true := scanChunk_append 0 49500 500 h c99
  have h : scanChunk 0 50500 = true := scanChunk_append 0 50000 500 h c100
  have h : scanChunk 0 51000 = true := scanChunk_append 0 50500 500 h c101
  have h : scanChunk 0 51500 = true := scanChunk_append 0 51000 500 h c102
  have h : scanChunk 0 52000 = true := scanChunk_append 0 51500 500 h c103
  have h : scanChunk 0 52500 = true := scanChunk_append 0 52000 500 h c104
  have h : scanChunk 0 53000 = true := scanChunk_append 0 52500 500 h c105
  have h : scanChunk 0 53500 = true := scanChunk_append 0 53000 500 h c106
  have h : scanChunk 0 54000 = true := scanChunk_append 0 53500 500 h c107
  have h : scanChunk 0 54500 = true := scanChunk_append 0 54000 500 h c108
  have h : scanChunk 0 55000 = true := scanChunk_append 0 54500 500 h c109
  have h : scanChunk 0 55500 = true := scanChunk_append 0 55000 500 h c110
  have h : scanChunk 0 56000 = true := scanChunk_append 0 55500 500 h c111
  have h : scanChunk 0 56500 = true := scanChunk_append 0 56000 500 h c112
  have h : scanChunk 0 57000 = true := scanChunk_append 0 56500 500 h c113
  have h : scanChunk 0 57500 = true := scanChunk_append 0 57000 500 h c114
  have h : scanChunk 0 58000 = true := scanChunk_append 0 57500 500 h c115
  have h : scanChunk 0 58500 = true := scanChunk_append 0 58000 500 h c116
  have h : scanChunk 0 59000 = true := scanChunk_append 0 58500 500 h c117
  have h : scanChunk 0 59500 = true := scanChunk_append 0 59000 500 h c118
  have h : scanChunk 0 60000 = true := scanChunk_append 0 59500 500 h c119
  have h : scanChunk 0 60500 = true := scanChunk_append 0 60000 500 h c120
  have h : scanChunk 0 61000 = true := scanChunk_append 0 60500 500 h c121
  have h : scanChunk 0 61500 = true := scanChunk_append 0 61000 500 h c122
  have h : scanChunk 0 62000 = true := scanChunk_append 0 61500 500 h c123
  have h : scanChunk 0 62500 = true := scanChunk_append 0 62000 500 h c124
  have h : scanChunk 0 63000 = true := scanChunk_append 0 62500 500 h c125
  have h : scanChunk 0 63500 = true := scanChunk_append 0 63000 500 h c126
  have h : scanChunk 0 64000 = true := scanChunk_append 0 63500 500 h c127
  have h : scanChunk 0 64500 = true := scanChunk_append 0 64000 500 h c128
  have h : scanChunk 0 65000 = true := scanChunk_append 0 64500 500 h c129
  have h : scanChunk 0 65500 = true := scanChunk_append 0 65000 500 h c130
  have h : scanChunk 0 66000 = true := scanChunk_append 0 65500 500 h c131
  have h : scanChunk 0 66500 = true := scanChunk_append 0 66000 500 h c132
  have h : scanChunk 0 67000 = true := scanChunk_append 0 66500 500 h c133
  have h : scanChunk 0 67500 = true := scanChunk_append 0 67000 500 h c134
  have h : scanChunk 0 68000 = true := scanChunk_append 0 67500 500 h c135
  have h : scanChunk 0 68500 = true := scanChunk_append 0 68000 500 h c136
  have h : scanChunk 0 69000 = true := scanChunk_append 0 68500 500 h c137
  have h : scanChunk 0 69500 = true := scanChunk_append 0 69000 500 h c138
  have h : scanChunk 0 70000 = true := scanChunk_append 0 69500 500 h c139
  have h : scanChunk 0 70500 = true := scanChunk_append 0 70000 500 h c140
  have h : scanChunk 0 71000 = true := scanChunk_append 0 70500 500 h c141
  have h : scanChunk 0 71500 = true := scanChunk_append 0 71000 500 h c142
  have h : scanChunk 0 72000 = true := scanChunk_append 0 71500 500 h c143
  have h : scanChunk 0 72500 = true := scanChunk_append 0 72000 500 h c144
  have h : scanChunk 0 73000 = true := scanChunk_append 0 72500 500 h c145
  have h : scanChunk 0 73500 = true := scanChunk_append 0 73000 500 h c146
  have h : scanChunk 0 74000 = true := scanChunk_append 0 73500 500 h c147
  have h : scanChunk 0 74500 = true := scanChunk_append 0 74000 500 h c148
  have h : scanChunk 0 75000 = true := scanChunk_append 0 74500 500 h c149
  have h : scanChunk 0 75500 = true := scanChunk_append 0 75000 500 h c150
  have h : scanChunk 0 76000 = true := scanChunk_append 0 75500 500 h c151
  have h : scanChunk 0 76500 = true := scanChunk_append 0 76000 500 h c152
  have h : scanChunk 0 77000 = true := scanChunk_append 0 76500 500 h c153
  have h : scanChunk 0 77500 = true := scanChunk_append 0 77000 500 h c154
  have h : scanChunk 0 78000 = true := scanChunk_append 0 77500 500 h c155
  have h : scanChunk 0 78500 = true := scanChunk_append 0 78000 500 h c156
  have h : scanChunk 0 79000 = true := scanChunk_append 0 78500 500 h c157
  have h : scanChunk 0 79500 = true := scanChunk_append 0 79000 500 h c158
  have h : scanChunk 0 80000 = true := scanChunk_append 0 79500 500 h c159
  have h : scanChunk 0 80500 = true := scanChunk_append 0 80000 500 h c160
  have h : scanChunk 0 81000 = true := scanChunk_append 0 80500 500 h c161
  have h : scanChunk 0 81500 = true := scanChunk_append 0 81000 500 h c162
  have h : scanChunk 0 82000 = true := scanChunk_append 0 81500 500 h c163
  have h : scanChunk 0 82500 = true := scanChunk_append 0 82000 500 h c164
  have h : scanChunk 0 83000 = true := scanChunk_append 0 82500 500 h c165
  have h : scanChunk 0 83500 = true := scanChunk_append 0 83000 500 h c166
  have h : scanChunk 0 84000 = true := scanChunk_append 0 83500 500 h c167
  have h : scanChunk 0 84500 = true := scanChunk_append 0 84000 500 h c168
  have h : scanChunk 0 85000 = true := scanChunk_append 0 84500 500 h c169
  have h : scanChunk 0 85500 = true := scanChunk_append 0 85000 500 h c170
  have h : scanChunk 0 86000 = true := scanChunk_append 0 85500 500 h c171
  have h : scanChunk 0 86500 = true := scanChunk_append 0 86000 500 h c172
  have h : scanChunk 0 87000 = true := scanChunk_append 0 86500 500 h c173
  have h : scanChunk 0 87500 = true := scanChunk_append 0 87000 500 h c174
  have h : scanChunk 0 88000 = true := scanChunk_append 0 87500 500 h c175
  have h : scanChunk 0 88500 = true := scanChunk_append 0 88000 500 h c176
  have h : scanChunk 0 89000 = true := scanChunk_append 0 88500 500 h c177
  have h : scanChunk 0 89500 = true := scanChunk_append 0 89000 500 h c178
  have h : scanChunk 0 90000 = true := scanChunk_append 0 89500 500 h c179
  have h : scanChunk 0 90500 = true := scanChunk_append 0 90000 500 h c180
  have h : scanChunk 0 91000 = true := scanChunk_append 0 90500 500 h c181
  have h : scanChunk 0 91500 = true := scanChunk_append 0 91000 500 h c182
  have h : scanChunk 0 92000 = true := scanChunk_append 0 91500 500 h c183
  have h : scanChunk 0 92500 = true := scanChunk_append 0 92000 500 h c184
  have h : scanChunk 0 93000 = true := scanChunk_append 0 92500 500 h c185
  have h : scanChunk 0 93500 = true := scanChunk_append 0 93000 500 h c186
  have h : scanChunk 0 94000 = true := scanChunk_append 0 93500 500 h c187
  have h : scanChunk 0 94500 = true := scanChunk_append 0 94000 500 h c188
  have h : scanChunk 0 95000 = true := scanChunk_append 0 94500 500 h c189
  have h : scanChunk 0 95500 = true := scanChunk_append 0 95000 500 h c190
  have h : scanChunk 0 96000 = true := scanChunk_append 0 95500 500 h c191
  have h : scanChunk 0 96500 = true := scanChunk_append 0 96000 500 h c192
  have h : scanChunk 0 97000 = true := scanChunk_append 0 96500 500 h c193
  have h : scanChunk 0 97500 = true := scanChunk_append 0 97000 500 h c194
  have h : scanChunk 0 98000 = true := scanChunk_append 0 97500 500 h c195
  have h : scanChunk 0 98500 = true := scanChunk_append 0 98000 500 h c196
  have h : scanChunk 0 99000 = true := scanChunk_append 0 98500 500 h c197
  have h : scanChunk 0 99500 = true := scanChunk_append 0 99000 500 h c198
  have h : scanChunk 0 100000 = true := scanChunk_append 0 99500 500 h c199
  exact h

/-- **Theorem.** Every covering of ℤ by finitely many congruence classes with distinct odd moduli
`> 1` has lcm of moduli exceeding 100000. Kernel-checked; no `native_decide`. -/
theorem odd_covering_lcm_gt_100000 (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d)
    (hodd : ∀ c ∈ S, Odd c.d) (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c')
    (hcov : CoversZ S) : 100000 < S.lcm (·.d) :=
  odd_covering_lcm_gt_of_scan 100000
    (fun L hL hodd => scanChunk_spec 0 100000 scan_100000 L (by omega) (by omega) hodd)
    S hgt hodd hinj hcov

end Covering
