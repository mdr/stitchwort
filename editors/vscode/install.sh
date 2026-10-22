#!/usr/bin/env bash
# Package this folder as a .vsix and install it into VS Code.
# Modern VS Code ignores folders symlinked into ~/.vscode/extensions, so the
# extension has to be installed with `code --install-extension`.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
(cd "$here" && npm ci --omit=dev)
version="$(sed -n 's/.*"version": *"\([^"]*\)".*/\1/p' "$here/package.json")"
out="$(mktemp -d)/stitchwort-$version.vsix"
python3 - "$here" "$out" "$version" <<'PY'
import os, sys, zipfile
src, out, version = sys.argv[1:4]
manifest = f'''<?xml version="1.0" encoding="utf-8"?>
<PackageManifest Version="2.0.0" xmlns="http://schemas.microsoft.com/developer/vsx-schema/2011">
  <Metadata>
    <Identity Language="en-US" Id="stitchwort" Version="{version}" Publisher="local"/>
    <DisplayName>Stitchwort</DisplayName>
    <Description xml:space="preserve">Syntax colouring and language server client for Stitchwort (.sw) files</Description>
    <Categories>Programming Languages</Categories>
    <Properties><Property Id="Microsoft.VisualStudio.Code.Engine" Value="^1.82.0"/></Properties>
  </Metadata>
  <Installation><InstallationTarget Id="Microsoft.VisualStudio.Code"/></Installation>
  <Dependencies/>
  <Assets><Asset Type="Microsoft.VisualStudio.Code.Manifest" Path="extension/package.json" Addressable="true"/></Assets>
</PackageManifest>'''
types = '''<?xml version="1.0" encoding="utf-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension=".json" ContentType="application/json"/><Default Extension=".js" ContentType="application/javascript"/><Default Extension=".md" ContentType="text/markdown"/><Default Extension=".ts" ContentType="text/plain"/><Default Extension=".txt" ContentType="text/plain"/><Default Extension=".yml" ContentType="text/plain"/><Default Extension=".cmd" ContentType="text/plain"/><Default Extension=".sh" ContentType="text/plain"/><Default Extension=".sw" ContentType="text/plain"/><Default Extension=".vsixmanifest" ContentType="text/xml"/></Types>'''
with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
    z.writestr("extension.vsixmanifest", manifest)
    z.writestr("[Content_Types].xml", types)
    for root, _, files in os.walk(src):
        if os.path.relpath(root, src).split(os.sep)[0] == "test":
            continue
        for f in files:
            if f == "install.sh" or "." not in f:  # extensionless (LICENSE) has no content type
                continue
            p = os.path.join(root, f)
            z.write(p, "extension/" + os.path.relpath(p, src))
PY
code --install-extension "$out" --force
echo "Installed. Reload VS Code (Developer: Reload Window)."
