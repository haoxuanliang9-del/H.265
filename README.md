# x265 (H.265/HEVC 编码器) 源码说明

源码来自 VideoLAN 官方仓库 `https://github.com/videolan/x265`（master 分支，2026-07-22 拉取）。

## 目录结构

```
H265源码/
├── source/                # 主源码
│   ├── CMakeLists.txt     # CMake 构建入口
│   ├── x265.cpp           # 命令行入口 (main)
│   ├── x265.h             # 公共 API
│   ├── x265cli.h          # CLI 参数定义
│   ├── encoder/           # 编码核心
│   │   ├── encoder.cpp        # x265_encoder_open / x265_encoder_encode
│   │   ├── frameencoder.cpp   # 单帧编码主流程
│   │   ├── analysis.cpp       # CU 分析 / 模式决策
│   │   ├── search.cpp         # 预测搜索 / 残差编码
│   │   ├── motion.cpp         # 运动估计 (ME)
│   │   ├── ratecontrol.cpp    # 码率控制 (CRF / VBR)
│   │   ├── entropy.cpp        # 熵编码 (CABAC)
│   │   ├── slicetype.cpp      # slice 类型 / 帧类型决策
│   │   ├── sao.cpp            # SAO 去块滤波
│   │   └── ...
│   ├── common/            # 通用代码 (像素、变换、预测、汇编优化)
│   │   ├── common.cpp         # 全局初始化
│   │   ├── dct.cpp            # 变换 / 量化
│   │   ├── predict.cpp        # 帧内预测
│   │   ├── pixel.cpp          # SAD / SATD 等
│   │   ├── lowres.cpp         # 下采样 / lookahead
│   │   └── x86/               # x86 汇编优化 (NASM)
│   ├── input/             # 输入处理 (yuv / y4m)
│   ├── output/            # 输出处理 (raw / y4m / mp4)
│   └── dynamicHDR10/      # HDR10+ 动态元数据
├── build-debug/           # ★ 构建产物 (Debug 版)
│   ├── x265.exe           # ★ 可执行文件 (78MB, -O0 -g3)
│   ├── libx265.dll        # 动态库
│   ├── libx265.a          # 静态库
│   ├── libx265.dll.a      # 导入库
│   ├── test.yuv           # 测试样本 (64×64, 10帧)
│   └── test.hevc          # 编码输出 (28KB)
├── doc/                   # 文档
└── readme.rst
```

调试入门建议入口：
- 编码主循环：[encoder/encoder.cpp](source/encoder/encoder.cpp) → `x265_encoder_encode`
- 单帧编码：[encoder/frameencoder.cpp](source/encoder/frameencoder.cpp) → `FrameEncoder::threadMain`
- CU 分析决策：[encoder/analysis.cpp](source/encoder/analysis.cpp) → `Analysis::compressCTU`
- 运动估计：[encoder/motion.cpp](source/encoder/motion.cpp) → `Motion::motionEstimate`
- 码率控制：[encoder/ratecontrol.cpp](source/encoder/ratecontrol.cpp) → `RateControl::rateControlFrame`
- 熵编码：[encoder/entropy.cpp](source/encoder/entropy.cpp) → `Entropy::encode`
- 帧类型决策：[encoder/slicetype.cpp](source/encoder/slicetype.cpp)

## 编译环境

- MSYS2 (`C:\msys64`)
- 工具链：`mingw-w64-x86_64-gcc` 16.1.0、`nasm` 3.02、`cmake` 4.4.0、`ninja` 1.13.2
- 构建模式：**Debug**（`-O0 -g3 -ggdb`，符号完整）

## 重新编译

```bash
# 在 MSYS2 bash 中
export PATH="/c/msys64/mingw64/bin:/c/msys64/usr/bin:$PATH"
cd "/c/Users/Administrator/Desktop/H265源码/H265源码/build-debug"

# 增量编译（改了源码后）
ninja -j$(nproc)

# 完全重新配置 + 编译
cd ..
rm -rf build-debug && mkdir build-debug && cd build-debug
cmake -G "Ninja" \
  -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
  -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_C_FLAGS="-O0 -g3 -ggdb" \
  -DCMAKE_CXX_FLAGS="-O0 -g3 -ggdb" \
  -DCMAKE_MAKE_PROGRAM=/c/msys64/mingw64/bin/ninja.exe \
  -DENABLE_SHARED=ON -DENABLE_CLI=ON -DENABLE_HDR10_PLUS=ON \
  "../source"
ninja -j$(nproc)
```

## 调试方式

**已为你配好** `.vscode/` 下完整配置：`launch.json`、`tasks.json`、`c_cpp_properties.json`、`settings.json`，开箱即用。

### 1. Trae / VSCode 断点调试（推荐）

1. 用 Trae 打开 `C:\Users\Administrator\Desktop\H265源码\H265源码`
2. 安装 C/C++ 扩展 `ms-vscode.cpptools`
3. 在任意源码行号左侧点一下（红点）设置断点，例如 [encoder/encoder.cpp:1607](source/encoder/encoder.cpp#L1607) `x265_encoder_encode` 入口
4. 按 `F5` 启动调试，左侧栏选择 `x265 encode (Debug)` 配置
5. 变量、调用栈、寄存器、断点全在 `Run and Debug` 侧栏实时显示

提供了 3 个 launch 配置：
- **`x265 encode (Debug)`** — 10 帧 main profile ultrafast 编码，标准调试入口
- **`x265 single frame`** — 只编 1 帧，跟进 single-frame 流程最方便
- **`gdb attach`** — attach 到已运行的 x265 进程

任务 (`Ctrl+Shift+P` → `Tasks: Run Task`)：
- `build x265 (ninja)` — 增量编译（保存 .cpp 后 `Ctrl+Shift+B` 即可重新构建）
- `rebuild x265 clean` — 全量清理重建
- `gen test.yuv` — 重新生成 64×64×10 帧的随机测试 YUV

### 2. 常用断点位置

| 想研究的内容 | 文件:行 | 函数 |
|---|---|---|
| 编码主入口 | [encoder.cpp:1607](source/encoder/encoder.cpp) | `x265_encoder_encode` |
| 单帧编码主循环 | [frameencoder.cpp](source/encoder/frameencoder.cpp) | `FrameEncoder::threadMain` |
| CTU 分析 / 模式决策 | [analysis.cpp](source/encoder/analysis.cpp) | `compressCTU` |
| 运动估计 | [motion.cpp](source/encoder/motion.cpp) | `motionEstimate` |
| 码率控制 | [ratecontrol.cpp](source/encoder/ratecontrol.cpp) | `rateControlFrame` |
| CABAC 熵编码 | [entropy.cpp](source/encoder/entropy.cpp) | `Entropy::encode` |
| 帧类型决策 | [slicetype.cpp](source/encoder/slicetype.cpp) | `Slice::decideSliceType` |
| 帧内预测 | [predict.cpp](source/common/predict.cpp) | `predIntraPlanar/PredAng` |
| 变换量化 | [dct.cpp](source/common/dct.cpp) | `dequant / quant` |

### 3. 直接用 gdb（命令行）

```bash
cd "/c/Users/Administrator/Desktop/H265源码/H265源码/build-debug"
/c/msys64/mingw64/bin/gdb.exe ./x265.exe
(gdb) break x265_encoder_encode
(gdb) run --profile main --preset ultrafast --input-res 64x64 --fps 30 --frames 1 -o single.hevc test.yuv
(gdb) n
(gdb) p *encoder
```

### 4. 多线程调试小贴士

x265 默认是 `frame-parallel + wavefront`，单步时其他线程也在跑。`launch.json` 里已经设了 `set scheduler-locking on`，单步时只动当前线程更稳。
若想全线程停住，把这条注释掉，或在 GDB 控制台手动：
```
(gdb) set scheduler-locking off
```

## 验证

`build-debug/` 下已带 `test.yuv`（64×64, 10帧随机 YUV420P）和 `test.hevc`（28KB main profile 码流），可用 VLC / ffprobe 验证。

## 编译时修改的源码

1. `source/CMakeLists.txt` 第 10、16 行：`cmake_policy(SET CMP0025/CMP0054 OLD)` → `NEW`（cmake 4.x 不再支持 OLD）
2. `source/dynamicHDR10/json11/json11.cpp`：添加 `#include <cstdint>`（GCC 16 严格要求显式包含）
