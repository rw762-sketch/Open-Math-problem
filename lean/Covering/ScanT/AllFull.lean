import Covering.TowerCheck
import Covering.ScanT.C0
import Covering.ScanT.C1
import Covering.ScanT.C2
import Covering.ScanT.C3
import Covering.ScanT.C4
import Covering.ScanT.C5
import Covering.ScanT.C6
import Covering.ScanT.C7
import Covering.ScanT.C8
import Covering.ScanT.C9
import Covering.ScanT.C10
import Covering.ScanT.C11
import Covering.ScanT.C12
import Covering.ScanT.C13
import Covering.ScanT.C14
import Covering.ScanT.C15
import Covering.ScanT.C16
import Covering.ScanT.C17
import Covering.ScanT.C18
import Covering.ScanT.C19
import Covering.ScanT.C20
import Covering.ScanT.C21
import Covering.ScanT.C22
import Covering.ScanT.C23
import Covering.ScanT.C24
import Covering.ScanT.C25
import Covering.ScanT.C26
import Covering.ScanT.C27
import Covering.ScanT.C28
import Covering.ScanT.C29
import Covering.ScanT.C30
import Covering.ScanT.C31
import Covering.ScanT.C32
import Covering.ScanT.C33
import Covering.ScanT.C34
import Covering.ScanT.C35
import Covering.ScanT.C36
import Covering.ScanT.C37
import Covering.ScanT.C38
import Covering.ScanT.C39
import Covering.ScanT.C40
import Covering.ScanT.C41
import Covering.ScanT.C42
import Covering.ScanT.C43
import Covering.ScanT.C44
import Covering.ScanT.C45
import Covering.ScanT.C46
import Covering.ScanT.C47
import Covering.ScanT.C48
import Covering.ScanT.C49
import Covering.ScanT.C50
import Covering.ScanT.C51
import Covering.ScanT.C52
import Covering.ScanT.C53
import Covering.ScanT.C54
import Covering.ScanT.C55
import Covering.ScanT.C56
import Covering.ScanT.C57
import Covering.ScanT.C58
import Covering.ScanT.C59
import Covering.ScanT.C60
import Covering.ScanT.C61
import Covering.ScanT.C62
import Covering.ScanT.C63
import Covering.ScanT.C64
import Covering.ScanT.C65
import Covering.ScanT.C66
import Covering.ScanT.C67
import Covering.ScanT.C68
import Covering.ScanT.C69
import Covering.ScanT.C70
import Covering.ScanT.C71
import Covering.ScanT.C72
import Covering.ScanT.C73
import Covering.ScanT.C74
import Covering.ScanT.C75
import Covering.ScanT.C76
import Covering.ScanT.C77
import Covering.ScanT.C78
import Covering.ScanT.C79
import Covering.ScanT.C80
import Covering.ScanT.C81
import Covering.ScanT.C82
import Covering.ScanT.C83
import Covering.ScanT.C84
import Covering.ScanT.C85
import Covering.ScanT.C86
import Covering.ScanT.C87
import Covering.ScanT.C88
import Covering.ScanT.C89
import Covering.ScanT.C90
import Covering.ScanT.C91
import Covering.ScanT.C92
import Covering.ScanT.C93
import Covering.ScanT.C94
import Covering.ScanT.C95
import Covering.ScanT.C96
import Covering.ScanT.C97
import Covering.ScanT.C98
import Covering.ScanT.C99
import Covering.ScanT.C100
import Covering.ScanT.C101
import Covering.ScanT.C102
import Covering.ScanT.C103
import Covering.ScanT.C104
import Covering.ScanT.C105
import Covering.ScanT.C106
import Covering.ScanT.C107
import Covering.ScanT.C108
import Covering.ScanT.C109
import Covering.ScanT.C110
import Covering.ScanT.C111
import Covering.ScanT.C112
import Covering.ScanT.C113
import Covering.ScanT.C114
import Covering.ScanT.C115
import Covering.ScanT.C116
import Covering.ScanT.C117
import Covering.ScanT.C118
import Covering.ScanT.C119
import Covering.ScanT.C120
import Covering.ScanT.C121
import Covering.ScanT.C122
import Covering.ScanT.C123
import Covering.ScanT.C124
import Covering.ScanT.C125
import Covering.ScanT.C126
import Covering.ScanT.C127
import Covering.ScanT.C128
import Covering.ScanT.C129
import Covering.ScanT.C130
import Covering.ScanT.C131
import Covering.ScanT.C132
import Covering.ScanT.C133
import Covering.ScanT.C134
import Covering.ScanT.C135
import Covering.ScanT.C136
import Covering.ScanT.C137
import Covering.ScanT.C138
import Covering.ScanT.C139
import Covering.ScanT.C140
import Covering.ScanT.C141
import Covering.ScanT.C142
import Covering.ScanT.C143
import Covering.ScanT.C144
import Covering.ScanT.C145
import Covering.ScanT.C146
import Covering.ScanT.C147
import Covering.ScanT.C148
import Covering.ScanT.C149
import Covering.ScanT.C150
import Covering.ScanT.C151
import Covering.ScanT.C152
import Covering.ScanT.C153
import Covering.ScanT.C154
import Covering.ScanT.C155
import Covering.ScanT.C156
import Covering.ScanT.C157
import Covering.ScanT.C158
import Covering.ScanT.C159
import Covering.ScanT.C160
import Covering.ScanT.C161
import Covering.ScanT.C162
import Covering.ScanT.C163
import Covering.ScanT.C164
import Covering.ScanT.C165
import Covering.ScanT.C166
import Covering.ScanT.C167
import Covering.ScanT.C168
import Covering.ScanT.C169
import Covering.ScanT.C170
import Covering.ScanT.C171
import Covering.ScanT.C172
namespace Covering
open ScanT

theorem AllFull_scan : scanChunk2 0 6891884 = true := by
  have h : scanChunk2 0 40000 = true := c0
  have h : scanChunk2 0 80000 = true := scanChunk2_append 0 40000 40000 h c1
  have h : scanChunk2 0 120000 = true := scanChunk2_append 0 80000 40000 h c2
  have h : scanChunk2 0 160000 = true := scanChunk2_append 0 120000 40000 h c3
  have h : scanChunk2 0 200000 = true := scanChunk2_append 0 160000 40000 h c4
  have h : scanChunk2 0 240000 = true := scanChunk2_append 0 200000 40000 h c5
  have h : scanChunk2 0 280000 = true := scanChunk2_append 0 240000 40000 h c6
  have h : scanChunk2 0 320000 = true := scanChunk2_append 0 280000 40000 h c7
  have h : scanChunk2 0 360000 = true := scanChunk2_append 0 320000 40000 h c8
  have h : scanChunk2 0 400000 = true := scanChunk2_append 0 360000 40000 h c9
  have h : scanChunk2 0 440000 = true := scanChunk2_append 0 400000 40000 h c10
  have h : scanChunk2 0 480000 = true := scanChunk2_append 0 440000 40000 h c11
  have h : scanChunk2 0 520000 = true := scanChunk2_append 0 480000 40000 h c12
  have h : scanChunk2 0 560000 = true := scanChunk2_append 0 520000 40000 h c13
  have h : scanChunk2 0 600000 = true := scanChunk2_append 0 560000 40000 h c14
  have h : scanChunk2 0 640000 = true := scanChunk2_append 0 600000 40000 h c15
  have h : scanChunk2 0 680000 = true := scanChunk2_append 0 640000 40000 h c16
  have h : scanChunk2 0 720000 = true := scanChunk2_append 0 680000 40000 h c17
  have h : scanChunk2 0 760000 = true := scanChunk2_append 0 720000 40000 h c18
  have h : scanChunk2 0 800000 = true := scanChunk2_append 0 760000 40000 h c19
  have h : scanChunk2 0 840000 = true := scanChunk2_append 0 800000 40000 h c20
  have h : scanChunk2 0 880000 = true := scanChunk2_append 0 840000 40000 h c21
  have h : scanChunk2 0 920000 = true := scanChunk2_append 0 880000 40000 h c22
  have h : scanChunk2 0 960000 = true := scanChunk2_append 0 920000 40000 h c23
  have h : scanChunk2 0 1000000 = true := scanChunk2_append 0 960000 40000 h c24
  have h : scanChunk2 0 1040000 = true := scanChunk2_append 0 1000000 40000 h c25
  have h : scanChunk2 0 1080000 = true := scanChunk2_append 0 1040000 40000 h c26
  have h : scanChunk2 0 1120000 = true := scanChunk2_append 0 1080000 40000 h c27
  have h : scanChunk2 0 1160000 = true := scanChunk2_append 0 1120000 40000 h c28
  have h : scanChunk2 0 1200000 = true := scanChunk2_append 0 1160000 40000 h c29
  have h : scanChunk2 0 1240000 = true := scanChunk2_append 0 1200000 40000 h c30
  have h : scanChunk2 0 1280000 = true := scanChunk2_append 0 1240000 40000 h c31
  have h : scanChunk2 0 1320000 = true := scanChunk2_append 0 1280000 40000 h c32
  have h : scanChunk2 0 1360000 = true := scanChunk2_append 0 1320000 40000 h c33
  have h : scanChunk2 0 1400000 = true := scanChunk2_append 0 1360000 40000 h c34
  have h : scanChunk2 0 1440000 = true := scanChunk2_append 0 1400000 40000 h c35
  have h : scanChunk2 0 1480000 = true := scanChunk2_append 0 1440000 40000 h c36
  have h : scanChunk2 0 1520000 = true := scanChunk2_append 0 1480000 40000 h c37
  have h : scanChunk2 0 1560000 = true := scanChunk2_append 0 1520000 40000 h c38
  have h : scanChunk2 0 1600000 = true := scanChunk2_append 0 1560000 40000 h c39
  have h : scanChunk2 0 1640000 = true := scanChunk2_append 0 1600000 40000 h c40
  have h : scanChunk2 0 1680000 = true := scanChunk2_append 0 1640000 40000 h c41
  have h : scanChunk2 0 1720000 = true := scanChunk2_append 0 1680000 40000 h c42
  have h : scanChunk2 0 1760000 = true := scanChunk2_append 0 1720000 40000 h c43
  have h : scanChunk2 0 1800000 = true := scanChunk2_append 0 1760000 40000 h c44
  have h : scanChunk2 0 1840000 = true := scanChunk2_append 0 1800000 40000 h c45
  have h : scanChunk2 0 1880000 = true := scanChunk2_append 0 1840000 40000 h c46
  have h : scanChunk2 0 1920000 = true := scanChunk2_append 0 1880000 40000 h c47
  have h : scanChunk2 0 1960000 = true := scanChunk2_append 0 1920000 40000 h c48
  have h : scanChunk2 0 2000000 = true := scanChunk2_append 0 1960000 40000 h c49
  have h : scanChunk2 0 2040000 = true := scanChunk2_append 0 2000000 40000 h c50
  have h : scanChunk2 0 2080000 = true := scanChunk2_append 0 2040000 40000 h c51
  have h : scanChunk2 0 2120000 = true := scanChunk2_append 0 2080000 40000 h c52
  have h : scanChunk2 0 2160000 = true := scanChunk2_append 0 2120000 40000 h c53
  have h : scanChunk2 0 2200000 = true := scanChunk2_append 0 2160000 40000 h c54
  have h : scanChunk2 0 2240000 = true := scanChunk2_append 0 2200000 40000 h c55
  have h : scanChunk2 0 2280000 = true := scanChunk2_append 0 2240000 40000 h c56
  have h : scanChunk2 0 2320000 = true := scanChunk2_append 0 2280000 40000 h c57
  have h : scanChunk2 0 2360000 = true := scanChunk2_append 0 2320000 40000 h c58
  have h : scanChunk2 0 2400000 = true := scanChunk2_append 0 2360000 40000 h c59
  have h : scanChunk2 0 2440000 = true := scanChunk2_append 0 2400000 40000 h c60
  have h : scanChunk2 0 2480000 = true := scanChunk2_append 0 2440000 40000 h c61
  have h : scanChunk2 0 2520000 = true := scanChunk2_append 0 2480000 40000 h c62
  have h : scanChunk2 0 2560000 = true := scanChunk2_append 0 2520000 40000 h c63
  have h : scanChunk2 0 2600000 = true := scanChunk2_append 0 2560000 40000 h c64
  have h : scanChunk2 0 2640000 = true := scanChunk2_append 0 2600000 40000 h c65
  have h : scanChunk2 0 2680000 = true := scanChunk2_append 0 2640000 40000 h c66
  have h : scanChunk2 0 2720000 = true := scanChunk2_append 0 2680000 40000 h c67
  have h : scanChunk2 0 2760000 = true := scanChunk2_append 0 2720000 40000 h c68
  have h : scanChunk2 0 2800000 = true := scanChunk2_append 0 2760000 40000 h c69
  have h : scanChunk2 0 2840000 = true := scanChunk2_append 0 2800000 40000 h c70
  have h : scanChunk2 0 2880000 = true := scanChunk2_append 0 2840000 40000 h c71
  have h : scanChunk2 0 2920000 = true := scanChunk2_append 0 2880000 40000 h c72
  have h : scanChunk2 0 2960000 = true := scanChunk2_append 0 2920000 40000 h c73
  have h : scanChunk2 0 3000000 = true := scanChunk2_append 0 2960000 40000 h c74
  have h : scanChunk2 0 3040000 = true := scanChunk2_append 0 3000000 40000 h c75
  have h : scanChunk2 0 3080000 = true := scanChunk2_append 0 3040000 40000 h c76
  have h : scanChunk2 0 3120000 = true := scanChunk2_append 0 3080000 40000 h c77
  have h : scanChunk2 0 3160000 = true := scanChunk2_append 0 3120000 40000 h c78
  have h : scanChunk2 0 3200000 = true := scanChunk2_append 0 3160000 40000 h c79
  have h : scanChunk2 0 3240000 = true := scanChunk2_append 0 3200000 40000 h c80
  have h : scanChunk2 0 3280000 = true := scanChunk2_append 0 3240000 40000 h c81
  have h : scanChunk2 0 3320000 = true := scanChunk2_append 0 3280000 40000 h c82
  have h : scanChunk2 0 3360000 = true := scanChunk2_append 0 3320000 40000 h c83
  have h : scanChunk2 0 3400000 = true := scanChunk2_append 0 3360000 40000 h c84
  have h : scanChunk2 0 3440000 = true := scanChunk2_append 0 3400000 40000 h c85
  have h : scanChunk2 0 3480000 = true := scanChunk2_append 0 3440000 40000 h c86
  have h : scanChunk2 0 3520000 = true := scanChunk2_append 0 3480000 40000 h c87
  have h : scanChunk2 0 3560000 = true := scanChunk2_append 0 3520000 40000 h c88
  have h : scanChunk2 0 3600000 = true := scanChunk2_append 0 3560000 40000 h c89
  have h : scanChunk2 0 3640000 = true := scanChunk2_append 0 3600000 40000 h c90
  have h : scanChunk2 0 3680000 = true := scanChunk2_append 0 3640000 40000 h c91
  have h : scanChunk2 0 3720000 = true := scanChunk2_append 0 3680000 40000 h c92
  have h : scanChunk2 0 3760000 = true := scanChunk2_append 0 3720000 40000 h c93
  have h : scanChunk2 0 3800000 = true := scanChunk2_append 0 3760000 40000 h c94
  have h : scanChunk2 0 3840000 = true := scanChunk2_append 0 3800000 40000 h c95
  have h : scanChunk2 0 3880000 = true := scanChunk2_append 0 3840000 40000 h c96
  have h : scanChunk2 0 3920000 = true := scanChunk2_append 0 3880000 40000 h c97
  have h : scanChunk2 0 3960000 = true := scanChunk2_append 0 3920000 40000 h c98
  have h : scanChunk2 0 4000000 = true := scanChunk2_append 0 3960000 40000 h c99
  have h : scanChunk2 0 4040000 = true := scanChunk2_append 0 4000000 40000 h c100
  have h : scanChunk2 0 4080000 = true := scanChunk2_append 0 4040000 40000 h c101
  have h : scanChunk2 0 4120000 = true := scanChunk2_append 0 4080000 40000 h c102
  have h : scanChunk2 0 4160000 = true := scanChunk2_append 0 4120000 40000 h c103
  have h : scanChunk2 0 4200000 = true := scanChunk2_append 0 4160000 40000 h c104
  have h : scanChunk2 0 4240000 = true := scanChunk2_append 0 4200000 40000 h c105
  have h : scanChunk2 0 4280000 = true := scanChunk2_append 0 4240000 40000 h c106
  have h : scanChunk2 0 4320000 = true := scanChunk2_append 0 4280000 40000 h c107
  have h : scanChunk2 0 4360000 = true := scanChunk2_append 0 4320000 40000 h c108
  have h : scanChunk2 0 4400000 = true := scanChunk2_append 0 4360000 40000 h c109
  have h : scanChunk2 0 4440000 = true := scanChunk2_append 0 4400000 40000 h c110
  have h : scanChunk2 0 4480000 = true := scanChunk2_append 0 4440000 40000 h c111
  have h : scanChunk2 0 4520000 = true := scanChunk2_append 0 4480000 40000 h c112
  have h : scanChunk2 0 4560000 = true := scanChunk2_append 0 4520000 40000 h c113
  have h : scanChunk2 0 4600000 = true := scanChunk2_append 0 4560000 40000 h c114
  have h : scanChunk2 0 4640000 = true := scanChunk2_append 0 4600000 40000 h c115
  have h : scanChunk2 0 4680000 = true := scanChunk2_append 0 4640000 40000 h c116
  have h : scanChunk2 0 4720000 = true := scanChunk2_append 0 4680000 40000 h c117
  have h : scanChunk2 0 4760000 = true := scanChunk2_append 0 4720000 40000 h c118
  have h : scanChunk2 0 4800000 = true := scanChunk2_append 0 4760000 40000 h c119
  have h : scanChunk2 0 4840000 = true := scanChunk2_append 0 4800000 40000 h c120
  have h : scanChunk2 0 4880000 = true := scanChunk2_append 0 4840000 40000 h c121
  have h : scanChunk2 0 4920000 = true := scanChunk2_append 0 4880000 40000 h c122
  have h : scanChunk2 0 4960000 = true := scanChunk2_append 0 4920000 40000 h c123
  have h : scanChunk2 0 5000000 = true := scanChunk2_append 0 4960000 40000 h c124
  have h : scanChunk2 0 5040000 = true := scanChunk2_append 0 5000000 40000 h c125
  have h : scanChunk2 0 5080000 = true := scanChunk2_append 0 5040000 40000 h c126
  have h : scanChunk2 0 5120000 = true := scanChunk2_append 0 5080000 40000 h c127
  have h : scanChunk2 0 5160000 = true := scanChunk2_append 0 5120000 40000 h c128
  have h : scanChunk2 0 5200000 = true := scanChunk2_append 0 5160000 40000 h c129
  have h : scanChunk2 0 5240000 = true := scanChunk2_append 0 5200000 40000 h c130
  have h : scanChunk2 0 5280000 = true := scanChunk2_append 0 5240000 40000 h c131
  have h : scanChunk2 0 5320000 = true := scanChunk2_append 0 5280000 40000 h c132
  have h : scanChunk2 0 5360000 = true := scanChunk2_append 0 5320000 40000 h c133
  have h : scanChunk2 0 5400000 = true := scanChunk2_append 0 5360000 40000 h c134
  have h : scanChunk2 0 5440000 = true := scanChunk2_append 0 5400000 40000 h c135
  have h : scanChunk2 0 5480000 = true := scanChunk2_append 0 5440000 40000 h c136
  have h : scanChunk2 0 5520000 = true := scanChunk2_append 0 5480000 40000 h c137
  have h : scanChunk2 0 5560000 = true := scanChunk2_append 0 5520000 40000 h c138
  have h : scanChunk2 0 5600000 = true := scanChunk2_append 0 5560000 40000 h c139
  have h : scanChunk2 0 5640000 = true := scanChunk2_append 0 5600000 40000 h c140
  have h : scanChunk2 0 5680000 = true := scanChunk2_append 0 5640000 40000 h c141
  have h : scanChunk2 0 5720000 = true := scanChunk2_append 0 5680000 40000 h c142
  have h : scanChunk2 0 5760000 = true := scanChunk2_append 0 5720000 40000 h c143
  have h : scanChunk2 0 5800000 = true := scanChunk2_append 0 5760000 40000 h c144
  have h : scanChunk2 0 5840000 = true := scanChunk2_append 0 5800000 40000 h c145
  have h : scanChunk2 0 5880000 = true := scanChunk2_append 0 5840000 40000 h c146
  have h : scanChunk2 0 5920000 = true := scanChunk2_append 0 5880000 40000 h c147
  have h : scanChunk2 0 5960000 = true := scanChunk2_append 0 5920000 40000 h c148
  have h : scanChunk2 0 6000000 = true := scanChunk2_append 0 5960000 40000 h c149
  have h : scanChunk2 0 6040000 = true := scanChunk2_append 0 6000000 40000 h c150
  have h : scanChunk2 0 6080000 = true := scanChunk2_append 0 6040000 40000 h c151
  have h : scanChunk2 0 6120000 = true := scanChunk2_append 0 6080000 40000 h c152
  have h : scanChunk2 0 6160000 = true := scanChunk2_append 0 6120000 40000 h c153
  have h : scanChunk2 0 6200000 = true := scanChunk2_append 0 6160000 40000 h c154
  have h : scanChunk2 0 6240000 = true := scanChunk2_append 0 6200000 40000 h c155
  have h : scanChunk2 0 6280000 = true := scanChunk2_append 0 6240000 40000 h c156
  have h : scanChunk2 0 6320000 = true := scanChunk2_append 0 6280000 40000 h c157
  have h : scanChunk2 0 6360000 = true := scanChunk2_append 0 6320000 40000 h c158
  have h : scanChunk2 0 6400000 = true := scanChunk2_append 0 6360000 40000 h c159
  have h : scanChunk2 0 6440000 = true := scanChunk2_append 0 6400000 40000 h c160
  have h : scanChunk2 0 6480000 = true := scanChunk2_append 0 6440000 40000 h c161
  have h : scanChunk2 0 6520000 = true := scanChunk2_append 0 6480000 40000 h c162
  have h : scanChunk2 0 6560000 = true := scanChunk2_append 0 6520000 40000 h c163
  have h : scanChunk2 0 6600000 = true := scanChunk2_append 0 6560000 40000 h c164
  have h : scanChunk2 0 6640000 = true := scanChunk2_append 0 6600000 40000 h c165
  have h : scanChunk2 0 6680000 = true := scanChunk2_append 0 6640000 40000 h c166
  have h : scanChunk2 0 6720000 = true := scanChunk2_append 0 6680000 40000 h c167
  have h : scanChunk2 0 6760000 = true := scanChunk2_append 0 6720000 40000 h c168
  have h : scanChunk2 0 6800000 = true := scanChunk2_append 0 6760000 40000 h c169
  have h : scanChunk2 0 6840000 = true := scanChunk2_append 0 6800000 40000 h c170
  have h : scanChunk2 0 6880000 = true := scanChunk2_append 0 6840000 40000 h c171
  have h : scanChunk2 0 6891884 = true := scanChunk2_append 0 6880000 11884 h c172
  exact h

/-- Every covering of ℤ by finitely many classes with distinct odd moduli > 1 has lcm > 6891884.
Mathematics kernel-checked; the scan uses native_decide. -/
theorem odd_covering_lcm_gt_6891884 (S : Finset Cls) (hgt : ∀ c ∈ S, 1 < c.d)
    (hodd : ∀ c ∈ S, Odd c.d) (hinj : ∀ c ∈ S, ∀ c' ∈ S, c.d = c'.d → c = c')
    (hcov : CoversZ S) : 6891884 < S.lcm (·.d) :=
  odd_covering_lcm_gt_of_scan2 6891884
    (fun L hL hodd => scanChunk2_spec 0 6891884 AllFull_scan L (by omega) (by omega) hodd)
    S hgt hodd hinj hcov

end Covering
