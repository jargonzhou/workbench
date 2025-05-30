/******************************************************************************
 *  Compilation:  javac StdAudioStereo.java
 *  Execution:    java StdAudioStereo
 *  Dependencies: none
 *
 *  Simple library for reading, writing, and manipulating audio.
 *
 *  Supported formats:
 *  https://www.oracle.com/java/technologies/javase/jmf-211-formats.html
 *
 ******************************************************************************/

package com.spike.algorithm.support.io;

import javax.sound.sampled.*;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.LinkedList;

/**
 * The {@code StdAudioStereo} class provides static methods for playing,
 * reading, and saving stereo audio.
 * It uses a simple audio model that allows
 * you to send one pair of samples (left channel and right channel)
 * to the sound card at a time. Each sample is a
 * real number between –1.0 and +1.0. The samples are played in real
 * time using a sampling rate of 44,100 Hz.
 * In addition to playing individual pairs of samples, standard audio supports
 * reading, writing, and playing audio files in a number of standard formats.
 * <p>
 * See {@link StdAudio} for a version that supports <em>monaural</em>
 * audio (one channel only).
 * <p>
 * <b>Getting started.</b>
 * To use this class, you must have {@code StdAudioStereo} in your Java classpath.
 * Here are three possible ways to do this:
 * <ul>
 * <li> If you ran our autoinstaller, use the commands
 * {@code javac-introcs} and {@code java-introcs} (or {@code javac-algs4}
 * and {@code java-algs4}) when compiling and executing. These commands
 * add {@code stdlib.jar} (or {@code algs4.jar}) to the Java classpath, which
 * provides access to {@code StdAudioStereo}.
 * <li> Download <a href = "https://introcs.cs.princeton.edu/java/code/stdlib.jar">stdlib.jar</a>
 * (or <a href = "https://algs4.cs.princeton.edu/code/algs4.jar">algs4.jar</a>)
 * and add it to the Java classpath.
 * <li> Download <a href = "https://introcs.cs.princeton.edu/java/stdlib/StdAudioStereo.java">StdAudioStereo.java</a>
 * and put it in the working directory.
 * </ul>
 * p>
 * As a test, cut-and-paste the following short program into your editor:
 * <pre>
 *  public class TestStdAudioStereo {
 *      public static void main(String[] args) {
 *          double freq1 = 440.0;
 *          double freq2 = 220.0;
 *          for (int i = 0; i &lt; StdAudioStereo.SAMPLE_RATE; i++) {
 *              double sampleLeft  = 0.5 * Math.sin(2 * Math.PI * freq1 * i / StdAudioStereo.SAMPLE_RATE);
 *              double sampleRight = 0.5 * Math.sin(2 * Math.PI * freq2 * i / StdAudioStereo.SAMPLE_RATE);
 *              StdAudioStereo.play(sampleLeft, sampleRight);
 *          }
 *          StdAudioStereo.drain();
 *      }
 *  }
 * </pre>
 * p>
 * If you compile and execute the program, you should hear a pure tone
 * whose frequency is <em>concert A</em> (440 Hz) in the left speaker
 * and the pitch <em>A</em><sub>3</sub> (220 Hz) in the right speaker.
 * <p>
 * p>
 * <b>Playing audio samples.</b>
 * You can use the following methods to play individual audio samples,
 * either in monaural or stereo:
 * <ul>
 * <li> {@link #play(double sample)}
 * <li> {@link #play(double[] samples)}
 * <li> {@link #play(double sampleLeft, double sampleRight)}
 * <li> {@link #play(double[] samplesLeft, double[] samplesRight)}
 * </ul>
 * p>
 * Each method sends the specified sample (or samples) to the sound card.
 * The individual samples are real numbers between –1.0 and +1.0. If a
 * sample is outside this range, it will be <em>clipped</em> (rounded to
 * –1.0 or +1.0). The samples are played in real time using a sampling
 * rate of 44,100 Hz.
 * <p>
 * p>
 * <b>Playing audio files.</b>
 * You can use the following method to play an audio file:
 * <ul>
 * <li> {@link #play(String filename)}
 * </ul>
 * p>
 * It plays an audio file (in WAVE, AU, AIFF, or MIDI format) and does
 * not return until the audio file is finished playing. This can produce
 * particularly striking programs with minimal code.
 * For example, the following code fragment plays a drum loop:
 *
 * <pre>
 *  while (true) {
 *      StdAudioStereo.play("BassDrum.wav");
 *      StdAudioStereo.play("SnareDrum.wav");
 *  }
 * </pre>
 * <p>
 * The individual audio files
 * (such as <a href = "https://introcs.cs.princeton.edu/java/stdlib/BassDrum.wav">BassDrum.wav</a>
 * and <a href = "https://introcs.cs.princeton.edu/java/stdlib/SnareDrum.wav">SnareDrum.wav</a>)
 * must be accessible to Java, typically
 * by being in the same directory as the {@code .class} file.
 * p>
 *
 * <b>Reading and writing audio files.</b>
 * You can read and write audio files using the following methods:
 * <ul>
 * <li> {@link #read(String filename)}
 * <li> {@link #save(String filename, double[] samples)}
 * <li> {@link #save(String filename, double[] samplesLeft, double[] samplesRight)}
 * </ul>
 * p>
 * The first method reads audio samples from an audio file
 * (in WAVE, AU, AIFF, or MIDI format)
 * and returns them as a double array with values between –1.0 and +1.0.
 * The second two method saves the audio samples in the specified double array to an
 * audio file (in WAVE, AU, or AIFF format), either in monaural or stereo.
 * <p>
 * p>
 * <b>Audio file formats.</b>
 * {@code StdAudioStereo} relies on the
 * <a href = "https://www.oracle.com/java/technologies/javase/jmf-211-formats.html">Java Media Framework</a>
 * for reading, writing, and playing audio files. You should be able to read or play files
 * in WAVE, AU, AIFF, and MIDI formats and save them to WAVE, AU, and AIFF formats.
 * The file extensions corresponding to WAVE, AU, AIFF, and MIDI files
 * are {@code .wav}, {@code .au}, {@code .aiff}, and {@code .midi},
 * respectively.
 * Some systems support additional audio file formats, but probably not MP3 or M4A.
 * p>
 * The Java Media Framework supports a variety of different <em>audio data formats</em>,
 * which includes
 * <ul>
 * <Li> the sampling rate (e.g., 44,100 Hz);
 * <li> the number of bits per sample per channel (e.g., 8-bit or 16-bit);
 * <li> the number of channels (e.g., monaural or stereo);
 * <li> the byte ordering (e.g., little endian or big endian); and
 * <li> the encoding scheme (typically linear PCM).
 * </ul>
 * p>
 * When saving files, {@code StdAudioStereo} uses a sampling rate of 44,100 Hz,
 * 16 bits per sample, stereo audio, little endian, and linear PCM encoding.
 * When reading files, {@code StdAudioStereo} converts to a sammpling rate of 44,100 Hz,
 * with 16 bits per sample.
 * <p>
 * p>
 * <b>Recording audio.</b>
 * You can use the following methods to record audio samples that are
 * played as a result of calls to
 * {@link #play(double sample)},
 * {@link #play(double sampleLeft, double sampleRight)},
 * {@link #play(double[] samples)},
 * {@link #play(double[] samplesLeft, double[] samplesRight)},
 * or {@link #play(String filename)}:
 * <ul>
 * <li> {@link #startRecording()}
 * <li> {@link #stopRecording()}
 * <li> {@link #getRecordingMono()}
 * <li> {@link #getRecordingLeft()}
 * <li> {@link #getRecordingRight()}
 * </ul>
 * p>
 * The method {@code startRecording()} begins recording audio.
 * The method {@code stopRecording()} stops recording.
 * After calling {@code stopRecording()}, you can access the
 * recorded left and right channels using
 * {@code getRecordingLeft()} and {@code getRecordingRight()}.
 * p>
 * {@code StdAudioStereo} does not currently support recording audio that calls
 * {@code playInBackground()}.
 * p>
 * <b>Playing audio files in a background thread.</b>
 * You can use the following methods to play an audio file in a background thread
 * (e.g., as a background score in your program).
 * <ul>
 * <li> {@link #playInBackground(String filename)}
 * <li> {@link #stopInBackground()}
 * </ul>
 * p>
 * Each call to the first method plays the specified sound in a separate background
 * thread. Unlike with the {@link play} methods, your program will not wait
 * for the samples to finish playing before continuing.
 * It supports playing an audio file in WAVE, AU, AIFF, or MIDI format.
 * It is possible to play
 * multiple audio files simultaneously (in separate background threads).
 * The second method stops the playing of all audio in background threads.
 * p>
 * <b>Draining standard audio.</b>
 * On some systems, your Java program may terminate before all of the samples have been
 * sent to the sound card. To prevent this, it is recommend that you call the
 * following method to indicate that you are done using standard audio:
 * <ul>
 * <li> {@link #drain()}
 * </ul>
 * p>
 * The method drains any samples queued to the sound card that have not yet been
 * sent to the sound card.
 * p>
 * <b>Reference.</b>
 * For additional documentation,
 * see <a href="https://introcs.cs.princeton.edu/15inout">Section 1.5</a> of
 * <em>Computer Science: An Interdisciplinary Approach</em>
 * by Robert Sedgewick and Kevin Wayne.
 * <p>
 *
 * @author Robert Sedgewick
 * @author Kevin Wayne
 */
public final class StdAudioStereo {

    /**
     * The sample rate: 44,100 Hz for CD quality audio.
     */
    public static final int SAMPLE_RATE = 44100;

    private static final int BYTES_PER_SAMPLE = 2;       // 16-bit audio
    private static final int BITS_PER_SAMPLE = 16;       // 16-bit audio
    private static final int MAX_16_BIT = 32768;
    private static final int BYTES_PER_FRAME = 4;        // 2 bytes per sample * 2 channels
    private static final int SAMPLE_BUFFER_SIZE = 4096;  // should be a multiple of frame size

    private static final int MONAURAL = 1;  // 1 channel
    private static final int STEREO = 2;    // 2 channels

    private static final boolean LITTLE_ENDIAN = false;
    private static final boolean BIG_ENDIAN = true;
    private static final boolean UNSIGNED = false;
    private static final boolean SIGNED = true;
    private static final boolean LEFT_CHANNEL = false;
    private static final boolean RIGHT_CHANNEL = true;

    private static SourceDataLine line;   // to play the sound
    private static byte[] buffer;         // our internal buffer
    private static int bufferSize = 0;    // number of samples currently in internal buffer

    // queue of background runnables
    private static LinkedList<BackgroundRunnable> backgroundRunnables = new LinkedList<>();

    // for recording audio
    private static QueueOfDoubles recordedSamplesLeft = null;
    private static QueueOfDoubles recordedSamplesRight = null;
    private static boolean isRecording = false;

    private StdAudioStereo() {
        // can not instantiate
    }

    // static initializer
    static {
        init();
    }

    // open up an audio stream
    private static void init() {
        try {
            // 44,100 Hz, 16-bit audio, monaural, signed PCM, little endian
            AudioFormat format = new AudioFormat((float) SAMPLE_RATE, BITS_PER_SAMPLE, STEREO, SIGNED, LITTLE_ENDIAN);
            DataLine.Info info = new DataLine.Info(SourceDataLine.class, format);

            line = (SourceDataLine) AudioSystem.getLine(info);
            line.open(format, SAMPLE_BUFFER_SIZE * BYTES_PER_SAMPLE);

            // the internal buffer is a fraction of the actual buffer size, this choice is arbitrary
            // it gets divided because we can't expect the buffered data to line up exactly with when
            // the sound card decides to push out its samples. The buffer length must be a multiple of 4.
            buffer = new byte[SAMPLE_BUFFER_SIZE * BYTES_PER_SAMPLE / 2];
        } catch (LineUnavailableException e) {
            System.out.println(e.getMessage());
        }

        // no sound gets made before this call
        line.start();
    }

    // get an AudioInputStream object from a file
    private static AudioInputStream getAudioInputStreamFromFile(String filename) {
        if (filename == null) {
            throw new IllegalArgumentException("filename is null");
        }

        try {
            // first try to read file from local file system
            File file = new File(filename);
            if (file.exists()) {
                return AudioSystem.getAudioInputStream(file);
            }

            // resource relative to .class file
            InputStream is1 = StdAudioStereo.class.getResourceAsStream(filename);
            if (is1 != null) {
                return AudioSystem.getAudioInputStream(is1);
            }

            // resource relative to classloader root
            InputStream is2 = StdAudioStereo.class.getClassLoader().getResourceAsStream(filename);
            if (is2 != null) {
                return AudioSystem.getAudioInputStream(is2);
            }

            // from URL (including jar file)
            URI uri = new URI(filename);
            if (uri.isAbsolute()) {
                URL url = uri.toURL();
                return AudioSystem.getAudioInputStream(url);
            } else throw new IllegalArgumentException("could not read audio file '" + filename + "'");
        } catch (IOException | URISyntaxException e) {
            throw new IllegalArgumentException("could not read audio file '" + filename + "'");
        } catch (UnsupportedAudioFileException e) {
            throw new IllegalArgumentException("file of unsupported audio file format: '" + filename + "'", e);
        }
    }

    /**
     * Sends any queued samples to the sound card.
     */
    public static void drain() {
        if (bufferSize > 0) {
            line.write(buffer, 0, bufferSize);
            bufferSize = 0;
        }
        line.drain();
    }


    /**
     * Closes standard audio.
     */
/*
    public static void close() {
        drain();
        line.stop();
    }
*/

    /**
     * Writes one stereo sample (between –1.0 and +1.0) to standard audio.
     * If the sample is outside the range, it will be clipped
     * (rounded to –1.0 or +1.0).
     *
     * @param sampleLeft  the left sample to play
     * @param sampleRight the right sample to play
     * @throws IllegalArgumentException if either
     *                                  {@code sampleLeft} or {@code sampleRight} is {@code Double.NaN}
     */
    public static void play(double sampleLeft, double sampleRight) {
        if (Double.isNaN(sampleLeft)) throw new IllegalArgumentException("sampleLeft is NaN");
        if (Double.isNaN(sampleRight)) throw new IllegalArgumentException("sampleRight is NaN");

        // clip if outside [-1, +1]
        if (sampleLeft < -1.0) sampleLeft = -1.0;
        if (sampleLeft > +1.0) sampleLeft = +1.0;
        if (sampleRight < -1.0) sampleRight = -1.0;
        if (sampleRight > +1.0) sampleRight = +1.0;

        // save sample if recording
        if (isRecording) {
            recordedSamplesLeft.enqueue(sampleLeft);
            recordedSamplesRight.enqueue(sampleRight);
        }

        // convert left sample to bytes
        short sLeft = (short) (MAX_16_BIT * sampleLeft);
        if (sampleLeft == 1.0) sLeft = Short.MAX_VALUE;   // special case since 32768 not a short
        buffer[bufferSize++] = (byte) sLeft;
        buffer[bufferSize++] = (byte) (sLeft >> 8);   // little endian

        // convert right sample to bytes
        short sRight = (short) (MAX_16_BIT * sampleRight);
        if (sampleRight == 1.0) sRight = Short.MAX_VALUE;
        buffer[bufferSize++] = (byte) sRight;
        buffer[bufferSize++] = (byte) (sRight >> 8);   // little endian

        // send to sound card if buffer is full
        if (bufferSize >= buffer.length) {
            line.write(buffer, 0, buffer.length);
            bufferSize = 0;
        }
    }

    /**
     * Writes one sample (between –1.0 and +1.0) to standard audio.
     * If the sample is outside the range, it will be clipped
     * (rounded to –1.0 or +1.0).
     *
     * @param sample the sample to play
     * @throws IllegalArgumentException if {@code sample} is {@code Double.NaN}
     */
    public static void play(double sample) {
        play(sample, sample);
    }

    /**
     * Writes the array of samples (between –1.0 and +1.0) to standard audio.
     * If a sample is outside the range, it will be clipped.
     *
     * @param samples the array of samples to play
     * @throws IllegalArgumentException if any sample is {@code Double.NaN}
     * @throws IllegalArgumentException if {@code samples} is {@code null}
     */
    public static void play(double[] samples) {
        if (samples == null) throw new IllegalArgumentException("argument to play() is null");
        for (int i = 0; i < samples.length; i++) {
            play(samples[i]);
        }
    }

    /**
     * Writes the array of stereo samples (between –1.0 and +1.0) to standard audio.
     * If a sample is outside the range, it will be clipped.
     *
     * @param samplesLeft  the array of samples for the left channel to play
     * @param samplesRight the array of samples for the right channel to play
     * @throws IllegalArgumentException if any sample is {@code Double.NaN}
     * @throws IllegalArgumentException if either
     *                                  {@code samplesLeft} or {@code samplesRight} is {@code null}
     * @throws IllegalArgumentException if {@code samplesLeft.length != samplesRight.length}
     */
    public static void play(double[] samplesLeft, double[] samplesRight) {
        if (samplesLeft == null) throw new IllegalArgumentException("argument to play() is null");
        if (samplesRight == null) throw new IllegalArgumentException("argument to play() is null");
        if (samplesLeft.length != samplesRight.length)
            throw new IllegalArgumentException("left and right arrays have different lengths");

        for (int i = 0; i < samplesLeft.length; i++) {
            play(samplesLeft[i], samplesRight[i]);
        }
    }

    /**
     * Plays an audio file (in WAVE, AU, AIFF, or MIDI format) and waits for it to finish.
     *
     * @param filename the name of the audio file
     * @throws IllegalArgumentException if unable to play {@code filename}
     * @throws IllegalArgumentException if {@code filename} is {@code null}
     */
    public static void play(String filename) {

        // may not work for streaming file formats
        if (isRecording) {
            double[] samplesLeft = readLeft(filename);
            double[] samplesRight = readRight(filename);
            for (double sample : samplesLeft)
                recordedSamplesLeft.enqueue(sample);
            for (double sample : samplesRight)
                recordedSamplesRight.enqueue(sample);
        }

        AudioInputStream ais = getAudioInputStreamFromFile(filename);
        SourceDataLine line = null;
        int BUFFER_SIZE = 4096; // 4K buffer
        try {
            AudioFormat audioFormat = ais.getFormat();
            DataLine.Info info = new DataLine.Info(SourceDataLine.class, audioFormat);
            line = (SourceDataLine) AudioSystem.getLine(info);
            line.open(audioFormat);
            line.start();
            byte[] samples = new byte[BUFFER_SIZE];
            int count = 0;
            while ((count = ais.read(samples, 0, BUFFER_SIZE)) != -1) {
                line.write(samples, 0, count);
            }
        } catch (IOException | LineUnavailableException e) {
            System.out.println(e);
        } finally {
            if (line != null) {
                line.drain();
                line.close();
            }
        }
    }


    // helper method to read the left or right channel from the given audio file and return as a double[]
    private static double[] readChannel(String filename, boolean channel) {
        // 4K buffer (must be a multiple of 4 for stereo)
        int READ_BUFFER_SIZE = 4096;

        // create AudioInputStream from file
        AudioInputStream fromAudioInputStream = getAudioInputStreamFromFile(filename);
        AudioFormat fromAudioFormat = fromAudioInputStream.getFormat();

        // normalize AudioInputStream to 44,100 Hz, 16-bit audio, stereo, signed PCM, little endian
        // https://docs.oracle.com/javase/tutorial/sound/converters.html
        AudioFormat toAudioFormat = new AudioFormat((float) SAMPLE_RATE, BITS_PER_SAMPLE, STEREO, SIGNED, LITTLE_ENDIAN);
        if (!AudioSystem.isConversionSupported(toAudioFormat, fromAudioFormat)) {
            throw new IllegalArgumentException("system cannot convert from " + fromAudioFormat + " to " + toAudioFormat);
        }
        AudioInputStream toAudioInputStream = AudioSystem.getAudioInputStream(toAudioFormat, fromAudioInputStream);

        // extract the audio data and convert to a double[] with each sample between -1 and +1
        try {
            QueueOfDoubles queue = new QueueOfDoubles();
            int count = 0;
            byte[] bytes = new byte[READ_BUFFER_SIZE];
            while ((count = toAudioInputStream.read(bytes, 0, READ_BUFFER_SIZE)) != -1) {
                // little endian, stereo (perhaps, for a future version that supports stereo)
                for (int i = 0; i < count / 4; i++) {
                    double left = ((short) (((bytes[4 * i + 1] & 0xFF) << 8) | (bytes[4 * i + 0] & 0xFF))) / ((double) MAX_16_BIT);
                    double right = ((short) (((bytes[4 * i + 3] & 0xFF) << 8) | (bytes[4 * i + 2] & 0xFF))) / ((double) MAX_16_BIT);
                    if (channel == LEFT_CHANNEL) queue.enqueue(left);
                    else queue.enqueue(right);
                }
            }
            toAudioInputStream.close();
            fromAudioInputStream.close();
            return queue.toArray();
        } catch (IOException ioe) {
            throw new IllegalArgumentException("could not read audio file '" + filename + "'", ioe);
        }
    }

    /**
     * Reads the audio samples (left channel) from an audio file
     * (in WAVE, AU, AIFF, or MIDI format)
     * and returns them as a double array with values between –1.0 and +1.0.
     * The file can be any audio file supported by the Java Media Framework;
     * if the audio data format is monaural,
     * then {@link readLeft(String filename)}
     * and {@link readRight(String filename)}
     * will return the same sequence of values.
     *
     * @param filename the name of the audio file
     * @return the array of samples
     */
    public static double[] readLeft(String filename) {
        return readChannel(filename, LEFT_CHANNEL);
    }

    /**
     * Reads the audio samples (right channel) from an audio file
     * (in WAVE, AU, AIFF, or MIDI format)
     * and returns them as a double array with values between –1.0 and +1.0.
     * The file can be any audio file supported by the Java Media Framework;
     * if the audio data format is monaural,
     * then {@link readLeft(String filename)}
     * and {@link readRight(String filename)}
     * will return the same sequence of values.
     *
     * @param filename the name of the audio file
     * @return the array of samples
     */
    public static double[] readRight(String filename) {
        return readChannel(filename, RIGHT_CHANNEL);
    }


    /**
     * Reads the audio samples from a file (in WAVE, AU, AIFF, or MIDI format)
     * and returns them as a double array with values between –1.0 and +1.0.
     * The samples returned use 16-bit audio data, a sampling rate of 44,100,
     * and monaural audio.
     * The file can be any audio file supported by the Java Media Framework;
     * if the audio data format is stereo, it is first converted
     * to monaural.
     *
     * @param filename the name of the audio file
     * @return the array of samples
     */
    public static double[] read(String filename) {
        // 4K buffer (must be a multiple of 2 for monaural)
        int READ_BUFFER_SIZE = 4096;

        // create AudioInputStream from file
        AudioInputStream fromAudioInputStream = getAudioInputStreamFromFile(filename);
        AudioFormat fromAudioFormat = fromAudioInputStream.getFormat();

        // normalize AudioInputStream to 44,100 Hz, 16-bit audio, monaural, signed PCM, little endian
        // https://docs.oracle.com/javase/tutorial/sound/converters.html
        AudioFormat toAudioFormat = new AudioFormat((float) SAMPLE_RATE, BITS_PER_SAMPLE, MONAURAL, SIGNED, LITTLE_ENDIAN);
        if (!AudioSystem.isConversionSupported(toAudioFormat, fromAudioFormat)) {
            throw new IllegalArgumentException("system cannot convert from " + fromAudioFormat + " to " + toAudioFormat);
        }
        AudioInputStream toAudioInputStream = AudioSystem.getAudioInputStream(toAudioFormat, fromAudioInputStream);

        // extract the audio data and convert to a double[] with each sample between -1 and +1
        try {
            QueueOfDoubles queue = new QueueOfDoubles();
            int count = 0;
            byte[] bytes = new byte[READ_BUFFER_SIZE];
            while ((count = toAudioInputStream.read(bytes, 0, READ_BUFFER_SIZE)) != -1) {

                // little endian, monaural
                for (int i = 0; i < count / 2; i++) {
                    double sample = ((short) (((bytes[2 * i + 1] & 0xFF) << 8) | (bytes[2 * i] & 0xFF))) / ((double) MAX_16_BIT);
                    queue.enqueue(sample);
                }
            }
            toAudioInputStream.close();
            fromAudioInputStream.close();
            return queue.toArray();
        } catch (IOException ioe) {
            throw new IllegalArgumentException("could not read audio file '" + filename + "'", ioe);
        }
    }


    // helper method to save a file in specifed format
    private static void save(String filename, byte[] data, AudioFormat format, long numberOfFrames) {
        try (ByteArrayInputStream bais = new ByteArrayInputStream(data);
             AudioInputStream ais = new AudioInputStream(bais, format, numberOfFrames)) {

            if (filename.endsWith(".wav") || filename.endsWith(".WAV")) {
                if (!AudioSystem.isFileTypeSupported(AudioFileFormat.Type.WAVE, ais)) {
                    throw new IllegalArgumentException("saving to WAVE file format is not supported on this system");
                }
                AudioSystem.write(ais, AudioFileFormat.Type.WAVE, new File(filename));
            } else if (filename.endsWith(".au") || filename.endsWith(".AU")) {
                if (!AudioSystem.isFileTypeSupported(AudioFileFormat.Type.AU, ais)) {
                    throw new IllegalArgumentException("saving to AU file format is not supported on this system");
                }
                AudioSystem.write(ais, AudioFileFormat.Type.AU, new File(filename));
            } else if (filename.endsWith(".aif") || filename.endsWith(".aiff") || filename.endsWith(".AIF") || filename.endsWith(".AIFF")) {
                if (!AudioSystem.isFileTypeSupported(AudioFileFormat.Type.AIFF, ais)) {
                    throw new IllegalArgumentException("saving to AIFF file format is not supported on this system");
                }
                AudioSystem.write(ais, AudioFileFormat.Type.AIFF, new File(filename));
            } else {
                throw new IllegalArgumentException("file extension for saving must be .wav, .au, or .aif");
            }
        } catch (IOException ioe) {
            throw new IllegalArgumentException("unable to save file '" + filename + "'", ioe);
        }
    }

    /**
     * Saves the audio samples as an <em>monaural</em> audio file
     * (in WAV, AU, or AIFF format).
     * The file extension type must be either {@code .wav}, {@code .au},
     * or {@code .aiff}.
     * The audio data format uses a sampling rate of 44,100 Hz, 16-bit audio,
     * monaural, signed PCM, ands little endian.
     *
     * @param filename the name of the audio file
     * @param samples  the array of samples to save
     * @throws IllegalArgumentException if unable to save {@code filename}
     * @throws IllegalArgumentException if {@code samples} is {@code null}
     * @throws IllegalArgumentException if {@code filename} is {@code null}
     * @throws IllegalArgumentException if {@code filename} extension is not
     *                                  {@code .wav}, {@code .au}, or {@code .aiff}.
     */
    public static void save(String filename, double[] samples) {
        if (filename == null) {
            throw new IllegalArgumentException("filename is null");
        }
        if (samples == null) {
            throw new IllegalArgumentException("samples[] is null");
        }
        if (filename.length() == 0) {
            throw new IllegalArgumentException("argument to save() is the empty string");
        }

        // assumes 16-bit samples with sample rate = 44,100 Hz
        // use 16-bit audio, monaural, signed PCM, little Endian
        AudioFormat format = new AudioFormat(SAMPLE_RATE, 16, MONAURAL, SIGNED, LITTLE_ENDIAN);
        byte[] data = new byte[2 * samples.length];
        for (int i = 0; i < samples.length; i++) {
            int temp = (short) (samples[i] * MAX_16_BIT);
            if (samples[i] == 1.0) temp = Short.MAX_VALUE;   // special case since 32768 not a short
            data[2 * i + 0] = (byte) temp;
            data[2 * i + 1] = (byte) (temp >> 8);   // little endian
        }

        // now save the file
        save(filename, data, format, samples.length);
    }


    /**
     * Saves the stereo samples as a <em>stereo</em> audio file
     * (in WAV, AU, or AIFF format).
     * The file extension type must be either {@code .wav}, {@code .au},
     * or {@code .aiff}.
     * The audio data format uses a sampling rate of 44,100 Hz, 16-bit audio,
     * stereo, signed PCM, ands little endian.
     *
     * @param filename     the name of the audio file
     * @param samplesLeft  the array of samples in left channel to save
     * @param samplesRight the array of samples in right channel to save
     * @throws IllegalArgumentException if unable to save {@code filename}
     * @throws IllegalArgumentException if {@code samplesLeft} is {@code null}
     * @throws IllegalArgumentException if {@code samplesRight} is {@code null}
     * @throws IllegalArgumentException if {@code samplesLeft.length != samplesRight.length}
     * @throws IllegalArgumentException if {@code filename} extension is not
     *                                  {@code .wav}, {@code .au}, or {@code .aiff}.
     */
    public static void save(String filename, double[] samplesLeft, double[] samplesRight) {
        if (filename == null) {
            throw new IllegalArgumentException("filename is null");
        }
        if (samplesLeft == null) {
            throw new IllegalArgumentException("samplesLeft[] is null");
        }
        if (samplesRight == null) {
            throw new IllegalArgumentException("samplesRight[] is null");
        }
        if (samplesLeft.length != samplesRight.length) {
            throw new IllegalArgumentException("input arrays have different lengths");
        }
        // assumes 16-bit samples with sample rate = 44,100 Hz
        // use 16-bit audio, monaural, signed PCM, little Endian
        AudioFormat format = new AudioFormat(SAMPLE_RATE, 16, STEREO, SIGNED, LITTLE_ENDIAN);
        byte[] data = new byte[4 * samplesLeft.length];
        for (int i = 0; i < samplesLeft.length; i++) {
            int tempLeft = (short) (samplesLeft[i] * MAX_16_BIT);
            int tempRight = (short) (samplesRight[i] * MAX_16_BIT);
            if (samplesLeft[i] == 1.0) tempLeft = Short.MAX_VALUE;   // special case since 32768 not a short
            if (samplesRight[i] == 1.0) tempRight = Short.MAX_VALUE;
            data[4 * i + 0] = (byte) tempLeft;
            data[4 * i + 1] = (byte) (tempLeft >> 8);   // little endian
            data[4 * i + 2] = (byte) tempRight;
            data[4 * i + 3] = (byte) (tempRight >> 8);
        }

        // now save the file
        save(filename, data, format, samplesLeft.length);
    }

    /**
     * Stops the playing of all audio files in background threads.
     */
    public static synchronized void stopInBackground() {
        for (BackgroundRunnable runnable : backgroundRunnables) {
            runnable.stop();
        }
        backgroundRunnables.clear();
    }

    /**
     * Plays an audio file (in WAVE, AU, AIFF, or MIDI format) in its own
     * background thread. Multiple audio files can be played simultaneously.
     *
     * @param filename the name of the audio file
     * @throws IllegalArgumentException if unable to play {@code filename}
     * @throws IllegalArgumentException if {@code filename} is {@code null}
     */
    public static synchronized void playInBackground(final String filename) {
        BackgroundRunnable runnable = new BackgroundRunnable(filename);
        new Thread(runnable).start();
        backgroundRunnables.add(runnable);
    }

    private static class BackgroundRunnable implements Runnable {
        private volatile boolean exit = false;
        private final String filename;

        public BackgroundRunnable(String filename) {
            this.filename = filename;
        }

        // https://www3.ntu.edu.sg/home/ehchua/programming/java/J8c_PlayingSound.html
        // play a wav or aif file
        // javax.sound.sampled.Clip fails for long clips (on some systems)
        public void run() {
            AudioInputStream ais = getAudioInputStreamFromFile(filename);

            SourceDataLine line = null;
            int BUFFER_SIZE = 4096; // 4K buffer

            try {
                AudioFormat audioFormat = ais.getFormat();
                DataLine.Info info = new DataLine.Info(SourceDataLine.class, audioFormat);
                line = (SourceDataLine) AudioSystem.getLine(info);
                line.open(audioFormat);
                line.start();
                byte[] samples = new byte[BUFFER_SIZE];
                int count = 0;
                while (!exit && (count = ais.read(samples, 0, BUFFER_SIZE)) != -1) {
                    line.write(samples, 0, count);
                }
            } catch (IOException | LineUnavailableException e) {
                System.out.println(e);
            } finally {
                if (line != null) {
                    line.drain();
                    line.close();
                }
                backgroundRunnables.remove(this);
            }
        }

        public void stop() {
            exit = true;
        }
    }


    /**
     * Loops an audio file (in WAVE, AU, AIFF, or MIDI format) in its
     * own background thread.
     *
     * @param filename the name of the audio file
     * @throws IllegalArgumentException if {@code filename} is {@code null}
     * @deprecated to be removed in a future update, as it doesn't interact
     * well with {@link #playInBackground(String filename)} or
     * {@link #stopInBackground()}.
     */
    @Deprecated
    public static synchronized void loopInBackground(String filename) {
        if (filename == null) throw new IllegalArgumentException();

        final AudioInputStream ais = getAudioInputStreamFromFile(filename);

        try {
            Clip clip = AudioSystem.getClip();
            // Clip clip = (Clip) AudioSystem.getLine(new Line.Info(Clip.class));
            clip.open(ais);
            clip.loop(Clip.LOOP_CONTINUOUSLY);
        } catch (IOException | LineUnavailableException e) {
            System.out.println(e);
        }

        // keep JVM open
        new Thread(new Runnable() {
            public void run() {
                while (true) {
                    try {
                        Thread.sleep(1000);
                    } catch (InterruptedException e) {
                        System.out.println(e);
                    }
                }
            }
        }).start();
    }


    /**
     * Starts recording audio samples.
     * This includes all calls to {@code play()} that take samples as arguments,
     * but not calls to {@code play()} that play audio files.
     *
     * @throws IllegalArgumentException if recording mode is already on
     */
    public static void startRecording() {
        if (!isRecording) {
            recordedSamplesLeft = new QueueOfDoubles();
            recordedSamplesRight = new QueueOfDoubles();
            isRecording = true;
        } else {
            throw new IllegalStateException("startRecording() must not be called twice in a row");
        }
    }

    /**
     * Stops recording audio samples.
     *
     * @throws IllegalArgumentException if recording mode is not currently on
     */
    public static void stopRecording() {
        if (isRecording) {
            isRecording = false;
        } else {
            throw new IllegalStateException("stopRecording() must be called after calling startRecording()");
        }
    }

    /**
     * Returns the array of samples that was recorded in the left channel in
     * between the last calls to {@link startRecording()} and {@link stopRecording()}.
     *
     * @return the array of samples
     * @throws IllegalArgumentException unless {@code startRecording} and
     *                                  {@code stopRecording} were previously called in the appropriate order
     */
    public static double[] getRecordingLeft() {
        if (recordedSamplesRight != null) {
            throw new IllegalStateException("getRecordingLeft() must be called after startRecording()");
        }

        if (isRecording) {
            throw new IllegalStateException("getRecordingLeft() must be called after stopRecording()");
        }

        double[] results = recordedSamplesLeft.toArray();
        return results;
    }

    /**
     * Returns the array of samples that was recorded in the right channel in
     * between the last calls to {@link startRecording()} and {@link stopRecording()}.
     *
     * @return the array of samples
     * @throws IllegalArgumentException unless {@code startRecording} and
     *                                  {@code stopRecording} were previously called in the appropriate order
     */
    public static double[] getRecordingRight() {
        if (recordedSamplesRight != null) {
            throw new IllegalStateException("getRecordingRight() must be called after startRecording()");
        }

        if (isRecording) {
            throw new IllegalStateException("getRecordingRight() must be called after stopRecording()");
        }

        double[] result = recordedSamplesRight.toArray();
        return result;
    }

    /**
     * Returns the array of samples that was recorded in the right channel in
     * between the last calls to {@link startRecording()} and {@link stopRecording()},
     * by taking the average of the samples in the left and right channels.
     *
     * @return the array of samples
     * @throws IllegalArgumentException unless {@code startRecording} and
     *                                  {@code stopRecording} were previously called in the appropriate order
     */
    public static double[] getRecordingMono() {
        if (recordedSamplesRight != null) {
            throw new IllegalStateException("getRecording() must be called after startRecording()");
        }

        if (isRecording) {
            throw new IllegalStateException("getRecording() must be called after stopRecording()");
        }

        double[] left = getRecordingLeft();
        double[] right = getRecordingRight();
        int n = left.length;
        double[] sum = new double[n];
        for (int i = 0; i < left.length; i++) {
            sum[i] = 0.5 * (left[i] + right[i]);
        }
        return sum;
    }

    /***************************************************************************
     * Helper class for reading and recording audio.
     ***************************************************************************/
    private static class QueueOfDoubles {
        private final static int INIT_CAPACITY = 16;
        private double[] a;   // array of doubles
        private int n;        // number of items in queue

        // create an empty queue
        public QueueOfDoubles() {
            a = new double[INIT_CAPACITY];
            n = 0;
        }

        // resize the underlying array holding the items
        private void resize(int capacity) {
            assert capacity >= n;
            double[] temp = new double[capacity];
            for (int i = 0; i < n; i++)
                temp[i] = a[i];
            a = temp;
        }

        // enqueue item onto the queue
        public void enqueue(double item) {
            if (n == a.length) resize(2 * a.length);    // double length of array if necessary
            a[n++] = item;                            // add item
        }


        // number of items in queue
        public int size() {
            return n;
        }

        // return the items as an array of length n
        public double[] toArray() {
            double[] result = new double[n];
            for (int i = 0; i < n; i++)
                result[i] = a[i];
            return result;
        }

    }


    /**
     * Test client - plays some sound files and concert A.
     *
     * @param args the command-line arguments (none should be specified)
     */
    public static void main(String[] args) {
        // 440 Hz (left speaker) and 220Hz (right speaker) for 1 second
        double freq1 = 440.0;
        double freq2 = 220.0;
        for (int i = 0; i <= StdAudioStereo.SAMPLE_RATE; i++) {
            double sampleLeft = 0.5 * Math.sin(2 * Math.PI * freq1 * i / StdAudioStereo.SAMPLE_RATE);
            double sampleRight = 0.5 * Math.sin(2 * Math.PI * freq2 * i / StdAudioStereo.SAMPLE_RATE);
            StdAudioStereo.play(sampleLeft, sampleRight);
        }


        // play some sound files
        String base = "https://introcs.cs.princeton.edu/java/stdlib/";
        StdAudioStereo.play(base + "test.wav");          // helicopter
        StdAudioStereo.play(StdAudioStereo.readLeft(base + "test.midi"), StdAudioStereo.readRight(base + "test.midi"));

        // a sound loop
        for (int i = 0; i < 10; i++) {
            StdAudioStereo.play(base + "BassDrum.wav");
            StdAudioStereo.play(base + "SnareDrum.wav");
        }

        // need to call this in non-interactive stuff so the program doesn't terminate
        // until all the sound leaves the speaker.
        StdAudioStereo.drain();
    }
}

/******************************************************************************
 *  Copyright 2002-2025, Robert Sedgewick and Kevin Wayne.
 *
 *  This file is part of algs4.jar, which accompanies the textbook
 *
 *      Algorithms, 4th edition by Robert Sedgewick and Kevin Wayne,
 *      Addison-Wesley Professional, 2011, ISBN 0-321-57351-X.
 *      http://algs4.cs.princeton.edu
 *
 *
 *  algs4.jar is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  algs4.jar is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with algs4.jar.  If not, see http://www.gnu.org/licenses.
 ******************************************************************************/
