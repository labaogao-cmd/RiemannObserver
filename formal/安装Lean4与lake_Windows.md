# 在 Windows 上安装 Lean 4 和 lake

`lake` 是 Lean 4 的构建工具，随 **elan**（Lean 版本管理器）一起安装。任选下面一种方式即可。

---

## 方式一：用 VS Code + Lean 4 扩展（推荐）

1. 安装 **VS Code**：https://code.visualstudio.com/
2. 在 VS Code 里安装 **Lean 4** 扩展：  
   按 `Ctrl+Shift+X` 打开扩展，搜索 **Lean 4**，安装 **leanprover.lean4**。
3. 扩展会提示安装 Lean（通过 elan），按提示点 **“Install Lean using Elan”** 或类似按钮，完成安装。
4. 安装完成后，在 **PowerShell** 或 **命令提示符** 里重新开一个窗口（或重启终端），进入项目执行：
   ```powershell
   cd c:\Users\yaoni\Desktop\RiemannObserver\formal
   lake build
   ```
   若提示“找不到 lake”，说明 elan 没加入 PATH，用下面的**方式二**装 elan，或先关掉 VS Code 再重新打开终端试一次。

---

## 方式二：用 PowerShell 安装 elan（命令行）

1. **以管理员身份**打开 PowerShell，执行（一行一行复制）：
   ```powershell
   Invoke-WebRequest -Uri "https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-pc-windows-msvc.zip" -OutFile "$env:TEMP\elan.zip" -UseBasicParsing
   Expand-Archive -Path "$env:TEMP\elan.zip" -DestinationPath "$env:USERPROFILE\.elan" -Force
   ```
2. 把 elan 加到当前用户的 PATH（复制整段执行一次即可）：
   ```powershell
   [Environment]::SetEnvironmentVariable("Path", $env:USERPROFILE + "\.elan\bin;" + [Environment]::GetEnvironmentVariable("Path", "User"), "User")
   ```
3. **关闭并重新打开** PowerShell（或重新开一个终端窗口），然后执行：
   ```powershell
   elan --version
   ```
   能显示版本号就说明 elan 装好了。
4. 进入 formal 目录并构建：
   ```powershell
   cd c:\Users\yaoni\Desktop\RiemannObserver\formal
   lake build
   ```
   第一次运行可能会自动下载 Lean 4 工具链，等几分钟即可。

---

## 若仍提示“找不到 lake”

- 确认已**重新打开** PowerShell/终端（PATH 才生效）。
- 若用方式一装的，在 VS Code 里打开 `formal/RiemannObserver.lean`，等右下角 Lean 服务器启动后，再在终端里试 `lake build`（有时 elan 会装到扩展自带的路径，只在 VS Code 终端里可用）。
- 手动检查 elan 是否在 PATH 里：
  ```powershell
  $env:Path -split ';' | Where-Object { $_ -like '*elan*' }
  ```
  若有输出且路径里有 `elan\bin`，说明 PATH 已含 elan；没有的话，把方式二的第 2 步再执行一遍，然后重启终端。

---

## 验证成功

在 `formal` 目录下执行 `lake build`，最后出现类似：

```
Build completed successfully.
```

即表示 Lean 4 代码通过类型检查和证明检查。

---

## 若出现 SSL 下载错误

若 `lake build` 时提示 **SSL connect error** 或 **CRYPT_E_REVOCATION_OFFLINE**，说明本机下载 Lean 4 工具链时证书检查失败（常见于公司网络、VPN）。可尝试：

- **关掉 VPN** 再执行一次 `lake build`
- 或用 **手机热点** 联网再执行 `lake build`
- 或在浏览器能打开 https://releases.lean-lang.org 的前提下再试

**说明**：`formal/lean-toolchain` 已改为具体版本 `leanprover/lean4:v4.14.0`，避免“no such release: lean4”错误。
