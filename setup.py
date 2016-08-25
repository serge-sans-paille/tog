from setuptools import setup

setup(name='tog',
      version='0.1',
      py_modules=['tog'],
      description='Hindley-Milner typing for scientific Python programs',
      author='serge-sans-paille',
      author_email='serge.guelton@telecom-bretagne.eu',
      url='https://github.com/serge-sans-paille/tog',
      license="BSD 3-Clause",
      classifiers=['Development Status :: 2 - Pre-Alpha',
                   'Environment :: Console',
                   'Intended Audience :: Developers',
                   'License :: OSI Approved :: BSD License',
                   'Natural Language :: English',
                   'Programming Language :: Python :: 2',
                   'Programming Language :: Python :: 3'],
      install_requires=['gast']
      )
