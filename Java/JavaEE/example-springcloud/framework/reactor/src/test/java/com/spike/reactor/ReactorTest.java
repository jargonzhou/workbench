package com.spike.reactor;

import org.junit.jupiter.api.Test;
import org.mockito.Mockito;
import org.reactivestreams.Publisher;
import org.reactivestreams.Subscription;
import reactor.core.Disposable;
import reactor.core.Disposables;
import reactor.core.publisher.BaseSubscriber;
import reactor.core.publisher.Flux;
import reactor.core.publisher.Hooks;
import reactor.core.publisher.Mono;
import reactor.core.scheduler.Scheduler;
import reactor.core.scheduler.Schedulers;
import reactor.test.StepVerifier;
import reactor.util.retry.Retry;

import java.time.Duration;
import java.util.concurrent.Callable;
import java.util.function.*;
import java.util.stream.Collector;

/**
 * <pre>
 * @see Mono
 * @see Flux
 *
 * @see reactor.core.Disposable
 * @see Disposables#swap()
 * @see reactor.core.Disposables#composite(Disposable...)
 *
 * @see BaseSubscriber
 * </pre>
 */
public class ReactorTest {
    @Test
    public void testMono() {
        // assembly-time instrumentation
        Hooks.onOperatorDebug();

        // org.reactivestreams.Publisher
        Mono<String> mono = Mono.just("A")
                .log() // logging
                ;

        StepVerifier.create(mono)
                .expectNextMatches(s -> s.equals("A"))
                .verifyComplete();
    }

    @Test
    public void testFlux() {
        Hooks.onOperatorDebug();

        // org.reactivestreams.Publisher
        Flux<String> flux = Flux.just("A", "B", "C")
                .log();

        StepVerifier.create(flux)
                .expectNext("A", "B", "C")
                .verifyComplete();
    }

    @Test
    public void testSubscriber() {
        CustomSubscriber<String> subscriber = Mockito.spy(new CustomSubscriber<>());
        Flux.just("A", "B", "C").subscribe(subscriber);

        Mockito.verify(subscriber, Mockito.times(3))
                .onNext(Mockito.anyString());
    }

    // org.reactivestreams.Subscriber
    // org.reactivestreams.Subscription
    // reactor.core.Disposable
    public static class CustomSubscriber<T> extends BaseSubscriber<T> {
        @Override
        public void hookOnSubscribe(Subscription subscription) {
            // request 1
            request(1);
        }

        @Override
        public void hookOnNext(T value) {
            System.err.println("onNext: " + value);

            // request 1
            request(1);
        }
    }

    //
    // operators:
    // transform existing sequence
    // peek at the sequence's processing
    // split and join Flux sequences
    // work with time
    // return data synchronously
    //

    /**
     * <pre>
     * @see Flux#map(Function)
     * @see Flux#cast(Class)
     * @see Flux#range(int, int)
     * @see Flux#index()
     * @see Flux#timestamp()
     *
     * @see Flux#filter(Predicate)
     * @see Flux#ignoreElements()
     * @see Flux#take(long)
     * @see Flux#take(Duration)
     * @see Flux#takeLast(int)
     * @see Flux#takeUntil(Predicate)
     * @see Flux#takeUntilOther(Publisher)
     * @see Flux#elementAt(int)
     * @see Flux#single()
     * @see Flux#skip(long)
     *
     * @see Flux#collect(Collector)
     * @see Flux#collectList()
     * @see Flux#collectMap(Function)
     * @see Flux#collectMultimap(Function)
     * @see Flux#repeat()
     * @see Flux#defaultIfEmpty(Object)
     * @see Flux#distinct()
     * @see Flux#distinctUntilChanged()
     *
     *
     * @see Flux#count()
     * @see Flux#all(Predicate)
     * @see Flux#any(Predicate)
     * @see Flux#reduce(BiFunction)
     * @see Flux#scan(BiFunction)
     * @see Flux#then()
     * @see Flux#thenMany(Publisher)
     * @see Flux#thenEmpty(Publisher)
     *
     * @see Flux#concat(Publisher[])
     * @see Flux#merge(Publisher[])
     * @see Flux#zip(Publisher, Publisher)
     * @see Flux#zipWithIterable(Iterable)
     * @see Flux#combineLatest(Function, Publisher[])
     *
     *
     * buffering: {@code Flux<List<T>>}
     * @see Flux#buffer(int)
     * windowing: {@code Flux<Flux<T>>}
     * @see Flux#window(int)
     * @see Flux#windowUntil(Predicate)
     * grouping: {@code Flux<GroupedFlux<K,T>>}
     * @see Flux#groupBy(Function)
     *
     *
     * @see Flux#flatMap(Function)
     * @see Flux#concatMap(Function)
     * @see Flux#flatMapSequential(Function)
     *
     * @see Flux#sample(Duration)
     *
     * @see Flux#toIterable()
     * @see Flux#toStream()
     * @see Flux#blockFirst()
     * @see Flux#blockLast()
     *
     * @see Flux#doOnNext(Consumer)
     * @see Flux#doOnComplete(Runnable)
     * @see Flux#doOnError(Consumer)
     * @see Flux#doOnSubscribe(Consumer)
     * @see Flux#doOnRequest(LongConsumer)
     * @see Flux#doOnCancel(Runnable)
     * @see Flux#doOnTerminate(Runnable)
     * @see Flux#doOnEach(Consumer)
     *
     * @see Flux#materialize()
     * @see Flux#dematerialize()
     *
     * @see Flux#push(Consumer)
     * @see Flux#create(Consumer)
     * @see Flux#generate(Consumer)
     * @see Flux#using(Callable, Function)
     * @see Flux#usingWhen(Publisher, Function, Function)
     *
     * @see Flux#onErrorReturn(Object)
     * @see Flux#onErrorResume(Function)
     * @see Flux#retry()
     * @see Flux#retryWhen(Retry)
     * @see Flux#timeout(Duration)
     *
     * @see Flux#onBackpressureBuffer()
     * @see Flux#onBackpressureDrop()
     * @see Flux#onBackpressureLatest()
     * @see Flux#onBackpressureError()
     * @see Flux#limitRate(int)
     * @see Flux#limitRequest(long)
     *
     * @see Flux#defer(Supplier)
     *
     * @see reactor.core.publisher.ConnectableFlux
     * @see Flux#publish()
     *
     * @see Flux#cache()
     *
     * @see Flux#share()
     *
     * @see Flux#interval(Duration)
     * @see Flux#delayElements(Duration)
     * @see Flux#delaySequence(Duration)
     * @see Flux#elapsed()
     *
     * @see Flux#transform(Function)
     * @see Flux#transformDeferred(Function)
     * </pre>
     */
    @Test
    public void testOperators() {

    }


    /**
     * <pre>
     * @see org.reactivestreams.Processor
     *
     * @see reactor.core.publisher.DirectProcessor
     * @see reactor.core.publisher.UnicastProcessor
     * @see reactor.core.publisher.EmitterProcessor
     * @see reactor.core.publisher.ReplayProcessor
     *
     * @see reactor.core.publisher.Sinks.Many
     * </pre>
     */
    @Test
    public void testProcessor() {

    }

    /**
     * <pre>
     * @see reactor.core.scheduler.Scheduler
     * @see Schedulers#single()
     * @see Schedulers#parallel()
     * @see Schedulers#boundedElastic()
     *
     * @see Flux#publishOn(Scheduler)
     * @see Flux#subscribeOn(Scheduler)
     *
     * @see Flux#parallel()
     * @see reactor.core.publisher.ParallelFlux#runOn(Scheduler)
     * </pre>
     */
    @Test
    public void testScheduler() {

    }

    /**
     * <pre>
     * @see reactor.util.context.Context
     * </pre>
     */
    @Test
    public void testContext() {

    }

    //
    // internals:
    // macro-fusion: assemble time, aim to replace one operator with another
    // micro-fusion: runtime, aim to reuse of shared resources
    //  reactor.core.Fuseable

}
