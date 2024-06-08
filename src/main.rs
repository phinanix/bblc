#![allow(dead_code)]

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Term{
    Lambda(Box<Term>),
    App(Box<Term>, Box<Term>),
    Index(u8)
}
use std::fmt::format;

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
        /*  */Term::Index(n) => *n,
    }
}

fn is_closed(term: &Term) -> bool {
    term_openness(term) == 0
}

fn substitute_level(body: Term, substituent: &Term, level: u8) -> Term {
    match body {
        Index(n) => {
            if level == n {
                substituent.clone()
            } else {
                Index(n)
            }
        },
        Lambda(x) => substitute_level(*x, substituent, level+1),
        App(x, y) => 
            App(Box::new(substitute_level(*x, substituent, level)), 
                Box::new(substitute_level(*y, substituent, level)))
    }
}

fn substitute(body: Term, substituent: &Term) -> Term {
    substitute_level(body, &substituent, 1)
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
                    Lambda(z) => Some(substitute(*z, &y)),
                }
            }
        },
    }
}

fn whnf_reduce(mut term: Term) -> (Term, u32) {
    let mut counter = 0; 
    while let Some(reduced_term) = whnf_reduce_step(term.clone()) {
        term = reduced_term;
        counter += 1;
    }
    (term, counter)
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
                Some(substitute(*z, &y))
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

fn nf_reduce(mut term: Term) -> (Term, u32) {
    let mut counter = 0;
    while let Some(reduced_term) = nf_reduce_step(term.clone()) {
        term = reduced_term;
        counter += 1;
    }
    (term, counter)
}


/* 
    dp relation: count(0, *) = 0, count (1, *) = 0
    count(x, y) = 
          if x > y then 1 else 0 
        + count(x-2, y+1)
        + sum (z from 0 to x-2) count(z, y) * count(x-2-z, y)
*/
fn dp_counting_terms_of_size_open(target_size: usize, target_openness: usize) -> u64 {
    //size is the first index, openness is the second
    let mut table = vec![];
    for size in 0..=target_size {
        table.push(vec![]);
        let max_openness = target_openness + (target_size - size) / 2;
        for _ in 0..=max_openness {
            table[size].push(u64::MAX);
        }
    }
    for size in 0..=1.min(target_size) {
        let max_openness = target_openness + (target_size - size) / 2;
        for openness in 0..=max_openness {
            table[size][openness] = 0;
        }
    }
    for size in 2..=target_size {
        let max_openness = target_openness + (target_size - size) / 2;
        for openness in 0..=max_openness {
            let index_term_count = if size == openness + 1 {1} else {0};
            let mut lambda_term_count = 0;
            for o in 0..=openness+1 {
                lambda_term_count += table[size-2][o];
            }
            table[size-2][openness+1];
            let mut app_term_count = 0;
            for z in 0..=(size-2) {
                app_term_count += table[z][openness] * table[size-2-z][openness];
            }
            table[size][openness] = index_term_count + lambda_term_count + app_term_count;
        }
    }
    dbg!(&table);
    table[target_size][target_openness]
}

fn print_term(term: Term) -> String {
    match term {
        Index(n) => n.to_string(),
        Lambda(x) => "λ".to_owned() + &print_term(*x),
        App(x, y) => format!("({}){}", print_term(*x), print_term(*y)),
    }
}

enum Token {
    Lambda, 
    Open, 
    Close,
    Index(u8)
}

fn tokenize(term_string: String) -> Vec<Token> {
    let mut out = Vec::new();
    for s in term_string.chars() {
        match s {
            'λ' => out.push(Token::Lambda),
            '(' => out.push(Token::Open), 
            ')' => out.push(Token::Close),
            c => {
                if c.is_ascii_digit() && c != '0' {
                    out.push(Token::Index(c.to_digit(10).expect("we checked it is a digit") as u8))
                } else {
                    panic!("passed invalid charaacter {}", c)
                }
            }
        }
    }
    out
}

fn parse_tokens_recur(tokens: &[Token]) -> Option<(Term, &[Token])> {
    let first_token = tokens.first().expect("no parsing empty tokens");
    match first_token {
        Token::Lambda => {
            if tokens.len() == 1 {
                None
            } else {
                let (rest_term, rest_tokens) = parse_tokens_recur(&tokens[1..])?;
                Some((Lambda(Box::new(rest_term)), rest_tokens))
            }
        },
        Token::Index(n) => {
            Some((Index(*n), &tokens[1..]))
        },
        Token::Open => {
            let (term_a, rest_tokens) = parse_tokens_recur(&tokens[1..])?;
            if let Some(Token::Close) = rest_tokens.first() {
                let (term_b, rest_tokens) = parse_tokens_recur(&rest_tokens[1..])?;
                Some((App(Box::new(term_a), Box::new(term_b)), rest_tokens))
            } else {
                None
            }
        },
        Token::Close => None,
    }
}

fn parse_tokens(tokens: &[Token]) -> Option<Term> {
    let (term, rest_tokens) = parse_tokens_recur(tokens)?;
    if rest_tokens.len() == 0 {
        Some(term) 
    } else {
        None
    }

}

//for now only works up to 9 de-bruijn, higher things could be done at some point
fn parse_term(term_string: String) -> Option<Term> {
    parse_tokens(&tokenize(term_string))
}

fn main() {
    println!("Hello, world!");
}

mod test {
    use super::*;
    
    #[test]
    fn terms_print() {
        let id = Lambda(Box::new(Index(1)));
        let zero = id.clone();
        let one = Lambda(Box::new(Lambda(Box::new(App(Box::new(Index(2)), Box::new(Index(1)))))));
        
        let id_str = "λ1";
        let one_str = "λλ(2)1";

        assert_eq!(print_term(id), id_str);
        assert_eq!(print_term(one), one_str);
    }

    #[test]
    fn terms_parse_round_trip() {
        let id = Lambda(Box::new(Index(1)));
        let one = Lambda(Box::new(Lambda(Box::new(App(Box::new(Index(2)), Box::new(Index(1)))))));

        assert_eq!(parse_term(print_term(id.clone())), Some(id));
        assert_eq!(parse_term(print_term(one.clone())), Some(one));

        let two = "λλ(2)(2)1";
        assert_eq!(print_term(parse_term(two.to_owned()).unwrap()), two);
        let three = "λλ(2)(2)(2)1";
        assert_eq!(print_term(parse_term(three.to_owned()).unwrap()), three);
        let plus_part = "((3)2)1";
        assert_eq!(print_term(parse_term(plus_part.to_owned()).unwrap()), plus_part);
        let plus = "λλλλ((4)2)((3)2)1";
        assert_eq!(print_term(parse_term(plus.to_owned()).unwrap()), plus);
    }

    #[test]
    fn term_counting_works() {
        let correct_ans = vec![0, 0, 0, 0, 1, 
                                         0, 1, 1, 3];
        let mut calculated_ans = vec![];
        for size in 0..=8 {
            dbg!(size);
            calculated_ans.push(dp_counting_terms_of_size_open(size, 0));
        }
        assert_eq!(correct_ans, calculated_ans);

    }

    /*
    functions to write:
        print term in a human readable way instead of de bruijn
        enumerate terms of a size
    tests still to write:
        term size
        term openness 
        is closed 
        substitute
        whnf reduction
        nf reduction
     */
}