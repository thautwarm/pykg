from setuptools import setup

with open('./README.rst', encoding='utf-8') as f:
    readme = f.read()

setup(
    name='reflect',
    version="1.2",
    keywords='reflection, project configuration, dependency resolution',
    description="A proposal Fable Python package manager",
    long_description=readme,
    license='MIT',
    url='https://github.com/thautwarm/reflect',
    author='thautwarm',
    author_email='twshere@outlook.com',
    py_modules=[
        "wisepy2"
    ],
    platforms='any',
    classifiers=[
        'Programming Language :: Python :: 3.6',
        'Programming Language :: Python :: 3.6',
        'Programming Language :: Python :: 3.7',
        'Programming Language :: Python :: 3.8',
        'Programming Language :: Python :: 3.9',
        'Programming Language :: Python :: 3.10',
        'Programming Language :: Python :: Implementation :: CPython'
    ],
    zip_safe=False)