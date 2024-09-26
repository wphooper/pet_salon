from setuptools import setup

with open("README.md") as f:
    long_description = f.read()

setup(
    name="pet_salon",
    author="W. Patrick Hooper",
    author_email="whooper@ccny.cuny.edu",
    description="Polytope Exchange Transformations in SageMath",
    long_description=long_description,
    long_description_content_type="text/markdown",
    version="0.0.4",
    url="https://github.com/wphooper/pet_salon",
    license="GNU General Public License, version 2",
    packages=[
        "pet_salon",
        "pet_salon.affine_gps",
    ],
    setup_requires=["wheel"],
    include_package_data=True,
    classifiers=[
        "Development Status :: 2 - Pre-Alpha",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)",
        "Operating System :: OS Independent",
        "Programming Language :: Python",
        "Topic :: Scientific/Engineering :: Mathematics",
    ],
    keywords="polytope exchange, polygon exchange, PET, piecewise isometry, piecewise affine",
)
