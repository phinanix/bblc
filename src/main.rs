
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Term{
    Lambda(Box<Term>),
    App(Box<Term>, Box<Term>),
    Index(u8)
}
use Term::*;

fn term_size(term: Term) -> u32 {
    match term {
        Term::Lambda(x) => 2 + term_size(*x),
        Term::App(x, y) => 2 + term_size(*x) + term_size(*y),
        Term::Index(n) => (n + 1).into(),
    }
}

fn term_openness(term: &Term) -> u8 {
    match term {
        Term::Lambda(x) => {
            let x_openness = term_openness(x);
            if x_openness == 0 {
                0
            } else {
                x_openness - 1
            }
        }
        Term::App(x, y) => term_openness(x).max(term_openness(y)),
        Term::Index(n) => *n,
    }
}

fn is_closed(term: &Term) -> bool {
    term_openness(term) == 0
}

fn substitute(body: Term, substituent: Term) -> Term {
    todo!()
}

// weak head normal form, E := (\x -> term) or (x term_1 . . . term_n)
// returns none if there is no reduction
fn whnf_reduce_step(term: Term) -> Option<Term> {
    match term {
        Lambda(_) => None,
        Index(_) => None,
        App(x, y) => {
            // we might need to reduce two things. first, reduce x to whnf. second, 
            // if that x is a lambda, then we need to substitute. 
            if let Some(x_reduced) = whnf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else {
                match *x {
                    App(_, _) => None,
                    Index(_) => None,
                    Lambda(z) => Some(substitute(*z, *y)),
                }
            }
        },
    }
}

// normal form, ie E = (\x. E) or x E_1 . . . E_n
// returns None if there is no reduction
fn nf_reduce_step(term: Term) -> Option<Term> {
    match term {
        Index(_) => None,
        Lambda(x) => if let Some(new_term) = nf_reduce_step(*x) {
            Some(Lambda(Box::new(new_term)))
        } else {
            None
        },
        App(x, y) => {
            // first reduce x to whnf, if it becomes a lambda, then substitute. 
            // otherwise, reduce first x, then y to nf. 
            if let Some(x_reduced) = whnf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else if let Lambda(z) = *x.clone() {
                Some(substitute(*z, *y))
            } else if let Some(x_reduced) = nf_reduce_step(*x.clone()) {
                Some(App(Box::new(x_reduced), y))
            } else if let Some(y_reduced) = nf_reduce_step(*y.clone()) {
                Some(App(x, Box::new(y_reduced)))
            } else {
                None
            }
        },
    }
}

fn main() {
    println!("Hello, world!");
}
