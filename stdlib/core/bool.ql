pub enum Bool = True {} | False {}

def or: Bool -> Bool -> Bool {
    or False {} False {} = False {}
    or _ _ = True {}
}
