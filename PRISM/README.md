## Intro

[PRISM](https://www.prismmodelchecker.org/) is a probabilistic model checker. It can find the probability of reaching a given end state natively, without us needing to dump the entire state graph and run a separate program. It can also output diagrams, show simulations, and more!

The catch? PRISM doesn't have strings, arrays, functions, or control flow. As such it can't handle interesting industrial problems and is mostly limited to academic research. But I find it neat and included a copy of the thread spec for fun.

You can download PRISM [here](https://www.prismmodelchecker.org/download.php) and read an introductory tutorial [here](https://www.prismmodelchecker.org/tutorial/). The download asks for a name and organization but it's not actually checked. 

## Notes

The only "interesting" thing about the model is that we represent multiple threads with multiple distinct `modules`. When multiple probabilistic actions are enabled, PRISM will pick one at random to happen. We can't tell PRISM to weight one module over another, it'll always be uniform. So instead we have to model the probabilities inside each module's actions with noops (`true`).

Consider two threads, where `state1=GET` and `state2=INC`. The four possible outcomes are:

```
0.5*p_get: state1'=INC
0.5*p_inc: true
0.5*p_get: true
0.5*p_inc: state2'=DONE
```

Since the two `true` steps *don't change the state*, they won't chance our analysis of the end-state probabilities.
