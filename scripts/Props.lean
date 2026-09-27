import Taylor

/-- Writes `Taylor.widgetProps` to `docs/props.json` for the browser version. -/
def main : IO Unit :=
  IO.FS.writeFile "docs/props.json" Taylor.widgetProps.compress
