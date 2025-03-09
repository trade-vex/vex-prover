pub mod instruction;
pub mod record;
pub mod state;
pub mod order_book;

/// Flattens a list containing combinations of
///  - F (single element)
///  - [F; N] (array of N elements)
///  - [[F; N]; M] (matrix of M arrays of N elements)
/// to a single [F; K] array, where K = N * M + N + 1
#[macro_export]
macro_rules! flatten {
    ($($x:expr),*) => {{
        let mut result = Vec::new();

        $(
            // Handle different input types
            flatten_single(&mut result, $x);
        )*

        result.try_into().unwrap()
    }};
}

// Helper function to handle different input types
pub fn flatten_single<F>(acc: &mut Vec<F>, input: impl Flatten<F>) {
    input.flatten(acc);
}

// Trait to abstract flattening behavior
pub trait Flatten<F> {
    fn flatten(&self, acc: &mut Vec<F>);
}

// Flattening for F
impl<F: Clone> Flatten<F> for F {
    fn flatten(&self, acc: &mut Vec<F>) {
        acc.push(self.clone());
    }
}

// Flattening for [F; N]
impl<F: Clone, const N: usize> Flatten<F> for [F; N] {
    fn flatten(&self, acc: &mut Vec<F>) {
        acc.extend_from_slice(self);
    }
}

// Flattening for [[F; WIDTH]; HEIGHT]
impl<F: Clone, const HEIGHT: usize, const WIDTH: usize> Flatten<F> for [[F; WIDTH]; HEIGHT] {
    fn flatten(&self, acc: &mut Vec<F>) {
        for row in self.iter() {
            acc.extend_from_slice(row);
        }
    }
}
