use bool

def main: unit {
    main = unit
}

def or: Bool -> Bool -> Bool {
    or False {} False {} = False {}
    or _ _ = True {}
}
