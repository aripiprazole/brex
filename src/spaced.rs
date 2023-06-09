pub enum Mode {
    Interperse,
    Before,
}

pub struct Spaced<'a, T>(pub Mode, pub &'static str, pub &'a [T])
where
    T: std::fmt::Display;

impl<'a, T> std::fmt::Display for Spaced<'a, T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Spaced(Mode::Interperse, string, slice) => {
                if !slice.is_empty() {
                    write!(f, "{}", slice[0])?;
                    for element in &slice[1..] {
                        write!(f, "{string}{element}")?;
                    }
                }
            }
            Spaced(Mode::Before, string, slice) => {
                for element in slice.iter() {
                    write!(f, "{string}{element}")?;
                }
            }
        }
        Ok(())
    }
}
