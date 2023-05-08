// aprox_eq Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use std::{
    fs::File,
    io::Write,
    thread::{self, JoinHandle},
};

fn main() {
    /// Floating point type of choice.
    type F = f64;

    /// Value of divisor to go up to from 1.
    const N: usize = 8192;

    /// Array of 1^-n values to determine the precision of values used as
    /// numerators, this will create decimals like so for 0.1 -> 0.1, 0.2 ...
    /// 0.9.
    const PRECISIONS: &[F] = &[
        1e-1 as F, 1e-2 as F, 1e-3 as F, 1e-4 as F, 1e-4 as F, 1e-5 as F, 1e-6 as F,
    ];

    /// Number of parallel threads to compute on.
    const THREADS: usize = 32;

    let mut commonality_file = File::create("commonality").unwrap();
    let mut comm_split_occurances = File::create("commonality_occurances").unwrap();
    let mut comm_split_error = File::create("commonality_error").unwrap();
    let mut average_err_file = File::create("average_err").unwrap();
    let mut handles: Vec<JoinHandle<[(usize, F); N / THREADS]>> = Vec::new();

    for offset in 0..THREADS {
        handles.push(thread::spawn(move || -> [(usize, F); N / THREADS] {
            println!("started thread {}", offset);

            let mut arr = [(0, 0 as F); N / THREADS];

            for i in 1..arr.len() {
                // Since each thread has the same loop they need to offset the
                // `i` value by their thread number.
                let n = (i * THREADS) + offset;

                println!("calculating for n = {} on thread {}", n, offset);

                // This will hold the calculated error for each loop.
                let mut err = vec![0 as F; PRECISIONS.len()];

                for dec in PRECISIONS {
                    for coefficiant in 1..10 {
                        // With DEC as 10 this will produce 0.1, 0.2, 0.3 ... 0.9
                        let x = dec * coefficiant as F;

                        // Divide by n and then multiply to what should be the that
                        // starting value of x.
                        let div = x / n as F;
                        let mul = div * n as F;

                        // Calculate how off we are from x.
                        let dif = (x - mul).abs();
                        err.push(dif);
                    }
                }

                // Average the error of all decimal values to n and record them
                // taking not of the value of n.
                let average = err.iter().sum::<f64>() / err.len() as F;
                arr[i] = (n, average);
            }

            // Return our array of n values to their average errors.
            arr
        }));
    }

    let mut acc = [0 as F; N];
    let mut ret: Vec<[(usize, F); N / THREADS]> = Vec::new();

    for h in handles {
        ret.push(h.join().unwrap());
    }

    for r in ret {
        for (i, v) in r {
            acc[i] = v;
        }
    }

    let mut most_common: Vec<(u64, F)> = Vec::new();

    for v in acc {
        average_err_file
            .write(format!("{}\n", v).into_bytes().as_slice())
            .unwrap();

        if most_common.iter().any(|x| x.1 == v) {
            most_common = most_common
                .iter()
                .map(|x| {
                    let mut x = x.clone();
                    if x.1 == v {
                        x.0 += 1
                    }

                    x
                })
                .collect();
        } else {
            most_common.push((1, v));
        }
    }

    most_common.sort_by(|(v0, _), (v1, _)| v0.cmp(v1));

    for v in most_common {
        commonality_file
            .write(format!("{}: {}\n", v.0, v.1).into_bytes().as_slice())
            .unwrap();
        comm_split_occurances
            .write(format!("{}\n", v.0).into_bytes().as_slice())
            .unwrap();
        comm_split_error
            .write(format!("{}\n", v.1).into_bytes().as_slice())
            .unwrap();
    }
}
