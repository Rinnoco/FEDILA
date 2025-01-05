# FEDILA

Welcome to FEDILA, a pioneering software solution designed to revolutionize analytic computations of the fundamental forces in the universe. Developed using Mathematica, FEDILA optimizes computations both in the continuum and on a spacetime lattice, paving the way for advanced research in Quantum Field Theories.

## Features

- **Optimized Computations**: Focuses on both continuum and discretized versions of theory on a spacetime lattice.
- **Flexible Mathematica Package**: Handles a diverse spectrum of renormalization schemes.
- **Advanced Renormalization Schemes**: Includes continuum Gauge Invariant Renormalization Scheme.
- **Supersymmetric Theories Support**: Capable of extracting information and performing calculations specific to Supersymmetric Theories.
- **Graph Theory Application**: Utilizes Graph Theory principles for efficient perturbative computations.
- **Multi-Scheme Feynman Diagram Calculations**: Ready to calculate Feynman diagrams across various renormalization schemes, theories, and regularizations including dimensional and lattice.

## Primary Goals

FEDILA aims to enrich the field of Quantum Field Theories by:
- **Enhancing Supersymmetric Field Computations**: Expanding the existing set of programs to encompass supersymmetric fields.
- **Incorporating Improved Lattice Actions**: Integrating features of improved lattice actions.
- **Extending Feynman Diagram Computations**: Supporting computations beyond one-loop order.

## Impact

The development of FEDILA not only accelerates research processes but also enables deeper exploration into theories such as Quantum Chromodynamics (QCD), Quantum Electrodynamics (QED), and their supersymmetric versions. This automation promotes richer educational experiences, providing researchers and students alike with a profound understanding of the fundamental interactions and properties of subatomic and composite particles.

## Installation

FEDILA is a Mathematica package designed for automating Feynman diagram calculations on the lattice.
To use this package, you must first install Mathematica. Refer to the official installation guide
for Wolfram Mathematica: https://reference.wolfram.com/language/tutorial/InstallingMathematica.html

## Steps to Get Started:

1. System Requirements:
   Ensure that your system meets the requirements for running Mathematica and that you have an appropriate version installed.

2. Installation:
   Download the FEDILA package from the official repository and follow these steps to install it:

    - Copy the `Fedila.tar.gz` file to your disk and unpack it:
      > gunzip Fedila.tar.gz
    
      > tar -xf Fedila.tar.gz

    - Change to the `Fedila` directory:
      > cd Fedila

    - Open the file `input.m` and replace `"username"` with your own username. Save the changes:
      > emacs input.m
      [Replace "username" with your username]

3. Configuration:
   For better organization of your calculations, create two additional directories within your project:
   > mkdir fortranfiles
   > mkdir outfiles

4. Load the Package:
   Open a Mathematica kernel and load the `input.m` file by providing the full path to the `Fedila` folder. Example:
   In[1]:= << /home/username/Fedila/input.m

   After loading, all the commands required for Feynman diagram calculations are available in the Mathematica kernel.
   Note that new commands introduced by FEDILA begin with a lowercase letter, unlike Mathematica's native commands,
   which begin with an uppercase letter.

Additional Notes:
-----------------

- Detailed installation instructions and further documentation are available in the `docs` folder within the package.
- Ensure that you follow all guidelines for replacing paths and usernames in `input.m` for proper functioning.

## Contributing

Interested in contributing to FEDILA? We welcome contributions from the community. Please read our contributing guidelines before submitting your pull request.

## License

FEDILA is released under an MIT license. Details about the licensing will be provided here.

## Contact

For support or to contact the developers, please visit our [website](https://rinnoco.com/projects/fedila.html) for FEDILA or reach out to us via email at [info@rinnoco.com](mailto:info@rinnoco.com).
